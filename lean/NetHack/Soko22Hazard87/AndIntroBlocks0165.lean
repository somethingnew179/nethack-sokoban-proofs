import NetHack.Soko22Hazard87.AndIntroBlocks0164
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro41250 (p : Pattern) (ha : d129434 p = 1) (hb : d181811 p = 1) : d184234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129429 q = 1) (hb : d181811 q = 1) : d184229 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129429, d184229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41249 q ha hb
    | true =>
      simp only [d129429, d184229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129430 q = 1) (hb : d181811 q = 1) : d184230 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129430, d184230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129430, d184230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129431 q = 1) (hb : d181811 q = 1) : d184231 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129431, d184231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129431, d184231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129432 q = 1) (hb : d181811 q = 1) : d184232 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129432, d184232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129432, d184232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129433 q = 1) (hb : d181811 q = 1) : d184233 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129433, d184233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129433, d184233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129434 q = 1) (hb : d181811 q = 1) : d184234 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129434, d184234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129434, d184234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41251 (p : Pattern) (ha : d129440 p = 1) (hb : d181811 p = 1) : d184240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129435 q = 1) (hb : d181811 q = 1) : d184235 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129435, d184235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41250 q ha hb
    | true =>
      simp only [d129435, d184235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129436 q = 1) (hb : d181811 q = 1) : d184236 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129436, d184236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129436, d184236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129437 q = 1) (hb : d181811 q = 1) : d184237 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129437, d184237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129437, d184237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129438 q = 1) (hb : d181811 q = 1) : d184238 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129438, d184238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129438, d184238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129439 q = 1) (hb : d181811 q = 1) : d184239 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129439, d184239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129439, d184239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129440 q = 1) (hb : d181811 q = 1) : d184240 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129440, d184240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129440, d184240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41252 (p : Pattern) (ha : d129446 p = 1) (hb : d181811 p = 1) : d184246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129441 q = 1) (hb : d181811 q = 1) : d184241 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129441, d184241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41251 q ha hb
    | true =>
      simp only [d129441, d184241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129442 q = 1) (hb : d181811 q = 1) : d184242 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129442, d184242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129442, d184242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129443 q = 1) (hb : d181811 q = 1) : d184243 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129443, d184243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129443, d184243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129444 q = 1) (hb : d181811 q = 1) : d184244 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129444, d184244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129444, d184244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129445 q = 1) (hb : d181811 q = 1) : d184245 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129445, d184245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129445, d184245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129446 q = 1) (hb : d181811 q = 1) : d184246 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129446, d184246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129446, d184246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41253 (p : Pattern) (ha : d129452 p = 1) (hb : d181811 p = 1) : d184252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129447 q = 1) (hb : d181811 q = 1) : d184247 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129447, d184247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41252 q ha hb
    | true =>
      simp only [d129447, d184247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129448 q = 1) (hb : d181811 q = 1) : d184248 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129448, d184248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129448, d184248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129449 q = 1) (hb : d181811 q = 1) : d184249 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129449, d184249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129449, d184249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129450 q = 1) (hb : d181811 q = 1) : d184250 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129450, d184250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129450, d184250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129451 q = 1) (hb : d181811 q = 1) : d184251 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129451, d184251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129451, d184251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129452 q = 1) (hb : d181811 q = 1) : d184252 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129452, d184252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129452, d184252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41254 (p : Pattern) (ha : d129458 p = 1) (hb : d181811 p = 1) : d184258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129453 q = 1) (hb : d181811 q = 1) : d184253 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129453, d184253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41253 q ha hb
    | true =>
      simp only [d129453, d184253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129454 q = 1) (hb : d181811 q = 1) : d184254 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129454, d184254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129454, d184254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129455 q = 1) (hb : d181811 q = 1) : d184255 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129455, d184255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129455, d184255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129456 q = 1) (hb : d181811 q = 1) : d184256 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129456, d184256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129456, d184256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129457 q = 1) (hb : d181811 q = 1) : d184257 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129457, d184257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129457, d184257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129458 q = 1) (hb : d181811 q = 1) : d184258 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129458, d184258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129458, d184258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41255 (p : Pattern) (ha : d129464 p = 1) (hb : d181811 p = 1) : d184264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129459 q = 1) (hb : d181811 q = 1) : d184259 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129459, d184259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41254 q ha hb
    | true =>
      simp only [d129459, d184259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129460 q = 1) (hb : d181811 q = 1) : d184260 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129460, d184260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129460, d184260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129461 q = 1) (hb : d181811 q = 1) : d184261 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129461, d184261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129461, d184261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129462 q = 1) (hb : d181811 q = 1) : d184262 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129462, d184262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129462, d184262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129463 q = 1) (hb : d181811 q = 1) : d184263 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129463, d184263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129463, d184263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129464 q = 1) (hb : d181811 q = 1) : d184264 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129464, d184264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129464, d184264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41256 (p : Pattern) (ha : d129470 p = 1) (hb : d181811 p = 1) : d184270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129465 q = 1) (hb : d181811 q = 1) : d184265 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129465, d184265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41255 q ha hb
    | true =>
      simp only [d129465, d184265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129466 q = 1) (hb : d181811 q = 1) : d184266 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129466, d184266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129466, d184266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129467 q = 1) (hb : d181811 q = 1) : d184267 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129467, d184267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129467, d184267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129468 q = 1) (hb : d181811 q = 1) : d184268 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129468, d184268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129468, d184268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129469 q = 1) (hb : d181811 q = 1) : d184269 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129469, d184269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129469, d184269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129470 q = 1) (hb : d181811 q = 1) : d184270 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129470, d184270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129470, d184270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41257 (p : Pattern) (ha : d182843 p = 1) (hb : d183573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9292 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d182840 q = 1) (hb : d183570 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182840, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d182840, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d182841 q = 1) (hb : d183571 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182841, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182841, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d182842 q = 1) (hb : d183572 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182842, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182842, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d182843 q = 1) (hb : d183573 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182843, d183573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d182843, d183573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h7 p ha hb
theorem andIntro41258 (p : Pattern) (ha : d182849 p = 1) (hb : d183579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182844 q = 1) (hb : d183574 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182844, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41257 q ha hb
    | true =>
      simp only [d182844, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d182845 q = 1) (hb : d183575 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182845, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182845, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182846 q = 1) (hb : d183576 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182846, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182846, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d182847 q = 1) (hb : d183577 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182847, d183577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182847, d183577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182848 q = 1) (hb : d183578 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182848, d183578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182848, d183578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182849 q = 1) (hb : d183579 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182849, d183579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182849, d183579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41259 (p : Pattern) (ha : d182855 p = 1) (hb : d183585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182850 q = 1) (hb : d183580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182850, d183580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41258 q ha hb
    | true =>
      simp only [d182850, d183580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d182851 q = 1) (hb : d183581 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182851, d183581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182851, d183581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182852 q = 1) (hb : d183582 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182852, d183582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182852, d183582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182853 q = 1) (hb : d183583 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182853, d183583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182853, d183583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182854 q = 1) (hb : d183584 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182854, d183584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182854, d183584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182855 q = 1) (hb : d183585 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182855, d183585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182855, d183585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41260 (p : Pattern) (ha : d182861 p = 1) (hb : d183591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182856 q = 1) (hb : d183586 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182856, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41259 q ha hb
    | true =>
      simp only [d182856, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d182857 q = 1) (hb : d183587 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182857, d183587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d182857, d183587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d182858 q = 1) (hb : d183588 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182858, d183588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182858, d183588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182859 q = 1) (hb : d183589 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182859, d183589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182859, d183589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d182860 q = 1) (hb : d183590 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182860, d183590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182860, d183590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d182861 q = 1) (hb : d183591 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182861, d183591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182861, d183591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41261 (p : Pattern) (ha : d182867 p = 1) (hb : d183597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182862 q = 1) (hb : d183592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182862, d183592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182862, d183592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41260 q ha hb
  have h2 (q : Pattern) (ha : d182863 q = 1) (hb : d183593 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182863, d183593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d182863, d183593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d182864 q = 1) (hb : d183594 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182864, d183594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182864, d183594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182865 q = 1) (hb : d183595 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182865, d183595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182865, d183595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182866 q = 1) (hb : d183596 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182866, d183596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182866, d183596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182867 q = 1) (hb : d183597 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182867, d183597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182867, d183597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41262 (p : Pattern) (ha : d182875 p = 1) (hb : d183605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d51989 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9325 q = 1) (hb : d51989 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d182872 q = 1) (hb : d183602 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182872, d183602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d182872, d183602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d182873 q = 1) (hb : d183603 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182873, d183603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182873, d183603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9292 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d182840 q = 1) (hb : d183570 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182840, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d182840, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d182841 q = 1) (hb : d183571 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182841, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d182841, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d182874 q = 1) (hb : d183604 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182874, d183604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182874, d183604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d182842 q = 1) (hb : d183572 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182842, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d182842, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d182875 q = 1) (hb : d183605 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182875, d183605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d182875, d183605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41263 (p : Pattern) (ha : d182881 p = 1) (hb : d183611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182876 q = 1) (hb : d183606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182876, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41262 q ha hb
    | true =>
      simp only [d182876, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41257 q ha hb
  have h2 (q : Pattern) (ha : d182877 q = 1) (hb : d183607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182877, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182877, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182878 q = 1) (hb : d183608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182878, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182878, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d182844 q = 1) (hb : d183574 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182844, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41257 q ha hb
    | true =>
      simp only [d182844, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182845 q = 1) (hb : d183575 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182845, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182845, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d182846 q = 1) (hb : d183576 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182846, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182846, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d182879 q = 1) (hb : d183609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182879, d183609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182879, d183609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d182847 q = 1) (hb : d183577 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182847, d183577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d182847, d183577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d182880 q = 1) (hb : d183610 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182880, d183610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d182880, d183610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d182881 q = 1) (hb : d183611 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182881, d183611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d182881, d183611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro41264 (p : Pattern) (ha : d182887 p = 1) (hb : d183617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182882 q = 1) (hb : d183612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182882, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41263 q ha hb
    | true =>
      simp only [d182882, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d182883 q = 1) (hb : d183613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182883, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182883, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182850 q = 1) (hb : d183580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182850, d183580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41258 q ha hb
    | true =>
      simp only [d182850, d183580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182851 q = 1) (hb : d183581 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182851, d183581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182851, d183581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d182884 q = 1) (hb : d183614 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182884, d183614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182884, d183614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d182885 q = 1) (hb : d183615 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182885, d183615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182885, d183615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d182886 q = 1) (hb : d183616 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182886, d183616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d182886, d183616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d182887 q = 1) (hb : d183617 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182887, d183617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d182887, d183617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41265 (p : Pattern) (ha : d182893 p = 1) (hb : d183623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182888 q = 1) (hb : d183618 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182888, d183618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41264 q ha hb
    | true =>
      simp only [d182888, d183618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41259 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d182856 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d182889 q = 1) (hb : d183619 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182889, d183619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d182889, d183619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d182856 q = 1) (hb : d183586 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182856, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41259 q ha hb
    | true =>
      simp only [d182856, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182857 q = 1) (hb : d183587 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182857, d183587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182857, d183587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182890 q = 1) (hb : d183620 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182890, d183620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182890, d183620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d182891 q = 1) (hb : d183621 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182891, d183621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182891, d183621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d182892 q = 1) (hb : d183622 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182892, d183622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182892, d183622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d182893 q = 1) (hb : d183623 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182893, d183623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182893, d183623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41266 (p : Pattern) (ha : d182899 p = 1) (hb : d183629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182894 q = 1) (hb : d183624 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182894, d183624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182894, d183624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41265 q ha hb
  have h2 (q : Pattern) (ha : d182895 q = 1) (hb : d183625 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182895, d183625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d182895, d183625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d182896 q = 1) (hb : d183626 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182896, d183626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182896, d183626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182897 q = 1) (hb : d183627 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182897, d183627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182897, d183627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182898 q = 1) (hb : d183628 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182898, d183628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182898, d183628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182899 q = 1) (hb : d183629 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182899, d183629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182899, d183629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41267 (p : Pattern) (ha : d182911 p = 1) (hb : d183641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52117 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52117 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9377 q = 1) (hb : d52117 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d182905 q = 1) (hb : d183635 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182905, d183635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d182905, d183635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d182906 q = 1) (hb : d183636 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182906, d183636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182906, d183636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51989 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d139 q = 1) (hb : d51989 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9325 q = 1) (hb : d51989 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d182872 q = 1) (hb : d183602 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182872, d183602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d182872, d183602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d182873 q = 1) (hb : d183603 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182873, d183603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d182873, d183603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d182907 q = 1) (hb : d183637 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182907, d183637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182907, d183637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101014 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9382 q = 1) (hb : d101014 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9383 q = 1) (hb : d101014 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d182908 q = 1) (hb : d183638 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182908, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d182908, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d182909 q = 1) (hb : d183639 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182909, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d182909, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d25 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9292 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d182840 q = 1) (hb : d183570 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182840, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d182840, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h21 (q : Pattern) (ha : d182841 q = 1) (hb : d183571 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182841, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d182841, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h22 (q : Pattern) (ha : d182910 q = 1) (hb : d183640 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182910, d183640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d182910, d183640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d182911 q = 1) (hb : d183641 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182911, d183641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d182911, d183641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41268 (p : Pattern) (ha : d182917 p = 1) (hb : d183647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182912 q = 1) (hb : d183642 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182912, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41267 q ha hb
    | true =>
      simp only [d182912, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41262 q ha hb
  have h2 (q : Pattern) (ha : d182913 q = 1) (hb : d183643 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182913, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182913, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182914 q = 1) (hb : d183644 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182914, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182914, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d182876 q = 1) (hb : d183606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182876, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41262 q ha hb
    | true =>
      simp only [d182876, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41257 q ha hb
  have h5 (q : Pattern) (ha : d182877 q = 1) (hb : d183607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182877, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182877, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d182878 q = 1) (hb : d183608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182878, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182878, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d182915 q = 1) (hb : d183645 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182915, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182915, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d182844 q = 1) (hb : d183574 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182844, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41257 q ha hb
    | true =>
      simp only [d182844, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d182845 q = 1) (hb : d183575 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182845, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182845, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d182846 q = 1) (hb : d183576 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182846, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182846, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d182879 q = 1) (hb : d183609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182879, d183609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d182879, d183609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d182916 q = 1) (hb : d183646 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182916, d183646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d182916, d183646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d182917 q = 1) (hb : d183647 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182917, d183647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d182917, d183647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41269 (p : Pattern) (ha : d182923 p = 1) (hb : d183653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182918 q = 1) (hb : d183648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182918, d183648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41268 q ha hb
    | true =>
      simp only [d182918, d183648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d182919 q = 1) (hb : d183649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182919, d183649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182919, d183649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182882 q = 1) (hb : d183612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182882, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41263 q ha hb
    | true =>
      simp only [d182882, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182883 q = 1) (hb : d183613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182883, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182883, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d182920 q = 1) (hb : d183650 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182920, d183650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182920, d183650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d182921 q = 1) (hb : d183651 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182921, d183651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182921, d183651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d182922 q = 1) (hb : d183652 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182922, d183652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d182922, d183652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d182923 q = 1) (hb : d183653 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182923, d183653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d182923, d183653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41270 (p : Pattern) (ha : d182929 p = 1) (hb : d183659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182882 q = 1) (hb : d183612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182882, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41263 q ha hb
    | true =>
      simp only [d182882, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d182883 q = 1) (hb : d183613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182883, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182883, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182926 q = 1) (hb : d183656 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182926, d183656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182926, d183656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182927 q = 1) (hb : d183657 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182927, d183657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182927, d183657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182928 q = 1) (hb : d183658 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182928, d183658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182928, d183658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182929 q = 1) (hb : d183659 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182929, d183659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182929, d183659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41271 (p : Pattern) (ha : d182935 p = 1) (hb : d183665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182924 q = 1) (hb : d183654 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182924, d183654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41269 q ha hb
    | true =>
      simp only [d182924, d183654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41264 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d182888 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d182925 q = 1) (hb : d183655 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182925, d183655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d182925, d183655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d182930 q = 1) (hb : d183660 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182930, d183660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41270 q ha hb
    | true =>
      simp only [d182930, d183660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182931 q = 1) (hb : d183661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182931, d183661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182931, d183661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182932 q = 1) (hb : d183662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182932, d183662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182932, d183662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d182933 q = 1) (hb : d183663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182933, d183663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182933, d183663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d182934 q = 1) (hb : d183664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182934, d183664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182934, d183664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d182935 q = 1) (hb : d183665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182935, d183665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182935, d183665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41272 (p : Pattern) (ha : d182941 p = 1) (hb : d183671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182856 q = 1) (hb : d183586 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182856, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41259 q ha hb
    | true =>
      simp only [d182856, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d182937 q = 1) (hb : d183667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182937, d183667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182937, d183667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182938 q = 1) (hb : d183668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182938, d183668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182938, d183668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182939 q = 1) (hb : d183669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182939, d183669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182939, d183669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d182940 q = 1) (hb : d183670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182940, d183670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182940, d183670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d182941 q = 1) (hb : d183671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182941, d183671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182941, d183671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41273 (p : Pattern) (ha : d182947 p = 1) (hb : d183677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182936 q = 1) (hb : d183666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182936, d183666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182936, d183666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41271 q ha hb
  have h2 (q : Pattern) (ha : d182942 q = 1) (hb : d183672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182942, d183672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182942, d183672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41272 q ha hb
  have h3 (q : Pattern) (ha : d182943 q = 1) (hb : d183673 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182943, d183673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d182943, d183673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d182944 q = 1) (hb : d183674 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182944, d183674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182944, d183674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182945 q = 1) (hb : d183675 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182945, d183675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182945, d183675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182946 q = 1) (hb : d183676 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182946, d183676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182946, d183676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d182947 q = 1) (hb : d183677 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182947, d183677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182947, d183677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41274 (p : Pattern) (ha : d182953 p = 1) (hb : d183683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182868 q = 1) (hb : d183598 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182868, d183598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182868, d183598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41261 q ha hb
  have h2 (q : Pattern) (ha : d182869 q = 1) (hb : d183599 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182869, d183599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182869, d183599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182870 q = 1) (hb : d183600 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182870, d183600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182870, d183600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d182871 q = 1) (hb : d183601 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182871, d183601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182871, d183601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d182900 q = 1) (hb : d183630 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182900, d183630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182900, d183630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41266 q ha hb
  have h6 (q : Pattern) (ha : d182901 q = 1) (hb : d183631 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182901, d183631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182901, d183631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d182902 q = 1) (hb : d183632 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182902, d183632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182902, d183632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d182903 q = 1) (hb : d183633 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182903, d183633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182903, d183633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d182904 q = 1) (hb : d183634 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182904, d183634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182904, d183634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d182948 q = 1) (hb : d183678 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182948, d183678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182948, d183678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41273 q ha hb
  have h11 (q : Pattern) (ha : d182949 q = 1) (hb : d183679 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182949, d183679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182949, d183679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d182950 q = 1) (hb : d183680 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182950, d183680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182950, d183680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d182951 q = 1) (hb : d183681 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182951, d183681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182951, d183681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d182952 q = 1) (hb : d183682 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182952, d183682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182952, d183682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d182953 q = 1) (hb : d183683 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182953, d183683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d182953, d183683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41275 (p : Pattern) (ha : d182962 p = 1) (hb : d183692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52289 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d52289 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9449 q = 1) (hb : d52289 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d182954 q = 1) (hb : d183684 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182954, d183684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d182954, d183684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d182955 q = 1) (hb : d183685 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182955, d183685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182955, d183685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101072 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9458 q = 1) (hb : d101072 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
    | true =>
      simp only [d9458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9459 q = 1) (hb : d101072 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d182956 q = 1) (hb : d183686 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182956, d183686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d182956, d183686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d182957 q = 1) (hb : d183687 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182957, d183687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d182957, d183687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d182958 q = 1) (hb : d183688 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182958, d183688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182958, d183688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9468 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9469 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d182959 q = 1) (hb : d183689 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182959, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d182959, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d182960 q = 1) (hb : d183690 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182960, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d182960, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101014 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d9382 q = 1) (hb : d101014 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9383 q = 1) (hb : d101014 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d182908 q = 1) (hb : d183638 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182908, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d182908, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h21 (q : Pattern) (ha : d182909 q = 1) (hb : d183639 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182909, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d182909, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h22 (q : Pattern) (ha : d182961 q = 1) (hb : d183691 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182961, d183691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d182961, d183691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d182962 q = 1) (hb : d183692 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182962, d183692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d182962, d183692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41276 (p : Pattern) (ha : d182966 p = 1) (hb : d183696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d101014 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9383 q = 1) (hb : d101014 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d182908 q = 1) (hb : d183638 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182908, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d182908, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d182909 q = 1) (hb : d183639 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182909, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182909, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9292 q = 1) (hb : d51876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d182840 q = 1) (hb : d183570 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182840, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d182840, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d182841 q = 1) (hb : d183571 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182841, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d182841, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d182910 q = 1) (hb : d183640 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182910, d183640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182910, d183640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d182842 q = 1) (hb : d183572 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182842, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d182842, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d182966 q = 1) (hb : d183696 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182966, d183696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d182966, d183696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41277 (p : Pattern) (ha : d182972 p = 1) (hb : d183702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182963 q = 1) (hb : d183693 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182963, d183693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41275 q ha hb
    | true =>
      simp only [d182963, d183693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41267 q ha hb
  have h2 (q : Pattern) (ha : d182964 q = 1) (hb : d183694 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182964, d183694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182964, d183694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182965 q = 1) (hb : d183695 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182965, d183695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182965, d183695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d182967 q = 1) (hb : d183697 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182967, d183697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41267 q ha hb
    | true =>
      simp only [d182967, d183697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41276 q ha hb
  have h5 (q : Pattern) (ha : d182968 q = 1) (hb : d183698 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182968, d183698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182968, d183698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d182969 q = 1) (hb : d183699 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182969, d183699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182969, d183699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d182970 q = 1) (hb : d183700 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182970, d183700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182970, d183700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d182912 q = 1) (hb : d183642 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182912, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41267 q ha hb
    | true =>
      simp only [d182912, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41262 q ha hb
  have h9 (q : Pattern) (ha : d182913 q = 1) (hb : d183643 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182913, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182913, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d182914 q = 1) (hb : d183644 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182914, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182914, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d182876 q = 1) (hb : d183606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182876, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41262 q ha hb
    | true =>
      simp only [d182876, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41257 q ha hb
  have h12 (q : Pattern) (ha : d182877 q = 1) (hb : d183607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182877, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182877, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d182878 q = 1) (hb : d183608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182878, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182878, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d182915 q = 1) (hb : d183645 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182915, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d182915, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d182971 q = 1) (hb : d183701 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182971, d183701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d182971, d183701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d182972 q = 1) (hb : d183702 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182972, d183702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d182972, d183702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro41278 (p : Pattern) (ha : d182977 p = 1) (hb : d183707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182912 q = 1) (hb : d183642 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182912, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41267 q ha hb
    | true =>
      simp only [d182912, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41262 q ha hb
  have h2 (q : Pattern) (ha : d182913 q = 1) (hb : d183643 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182913, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182913, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182914 q = 1) (hb : d183644 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182914, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182914, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d182876 q = 1) (hb : d183606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182876, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41262 q ha hb
    | true =>
      simp only [d182876, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41257 q ha hb
  have h5 (q : Pattern) (ha : d182877 q = 1) (hb : d183607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182877, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182877, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d182878 q = 1) (hb : d183608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182878, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182878, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d182915 q = 1) (hb : d183645 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182915, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182915, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d182975 q = 1) (hb : d183705 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182975, d183705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d182975, d183705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d182976 q = 1) (hb : d183706 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182976, d183706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d182976, d183706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d182977 q = 1) (hb : d183707 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182977, d183707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d182977, d183707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro41279 (p : Pattern) (ha : d182983 p = 1) (hb : d183713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182973 q = 1) (hb : d183703 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182973, d183703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41277 q ha hb
    | true =>
      simp only [d182973, d183703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d182974 q = 1) (hb : d183704 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182974, d183704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182974, d183704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182978 q = 1) (hb : d183708 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182978, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41278 q ha hb
    | true =>
      simp only [d182978, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182979 q = 1) (hb : d183709 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182979, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182979, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d182980 q = 1) (hb : d183710 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182980, d183710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182980, d183710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d182981 q = 1) (hb : d183711 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182981, d183711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182981, d183711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d182982 q = 1) (hb : d183712 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182982, d183712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d182982, d183712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d182983 q = 1) (hb : d183713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182983, d183713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d182983, d183713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41280 (p : Pattern) (ha : d182985 p = 1) (hb : d183715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182876 q = 1) (hb : d183606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182876, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41262 q ha hb
    | true =>
      simp only [d182876, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41257 q ha hb
  have h2 (q : Pattern) (ha : d182877 q = 1) (hb : d183607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182877, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182877, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182878 q = 1) (hb : d183608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182878, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182878, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d182975 q = 1) (hb : d183705 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182975, d183705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182975, d183705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182984 q = 1) (hb : d183714 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182984, d183714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182984, d183714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182985 q = 1) (hb : d183715 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182985, d183715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182985, d183715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41281 (p : Pattern) (ha : d182991 p = 1) (hb : d183721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182978 q = 1) (hb : d183708 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182978, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41278 q ha hb
    | true =>
      simp only [d182978, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d182979 q = 1) (hb : d183709 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182979, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182979, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182986 q = 1) (hb : d183716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182986, d183716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41280 q ha hb
    | true =>
      simp only [d182986, d183716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182987 q = 1) (hb : d183717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182987, d183717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182987, d183717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d182988 q = 1) (hb : d183718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182988, d183718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182988, d183718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d182989 q = 1) (hb : d183719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182989, d183719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182989, d183719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d182990 q = 1) (hb : d183720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182990, d183720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d182990, d183720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d182991 q = 1) (hb : d183721 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182991, d183721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d182991, d183721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41282 (p : Pattern) (ha : d183002 p = 1) (hb : d183727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182978 q = 1) (hb : d183708 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182978, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41278 q ha hb
    | true =>
      simp only [d182978, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d182979 q = 1) (hb : d183709 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182979, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182979, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182999 q = 1) (hb : d183724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182999, d183724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182999, d183724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183000 q = 1) (hb : d183725 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183000, d183725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183000, d183725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183001 q = 1) (hb : d183726 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183001, d183726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183001, d183726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183002 q = 1) (hb : d183727 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183002, d183727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183002, d183727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41283 (p : Pattern) (ha : d183008 p = 1) (hb : d183733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182992 q = 1) (hb : d183722 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182992, d183722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41279 q ha hb
    | true =>
      simp only [d182992, d183722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41281 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d182997 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d182998 q = 1) (hb : d183723 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182998, d183723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d182998, d183723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d183003 q = 1) (hb : d183728 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183003, d183728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41282 q ha hb
    | true =>
      simp only [d183003, d183728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183004 q = 1) (hb : d183729 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183004, d183729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183004, d183729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183005 q = 1) (hb : d183730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183005, d183730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183005, d183730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183006 q = 1) (hb : d183731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183006, d183731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183006, d183731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183007 q = 1) (hb : d183732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183007, d183732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183007, d183732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183008 q = 1) (hb : d183733 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183008, d183733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183008, d183733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41284 (p : Pattern) (ha : d182996 p = 1) (hb : d183738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182986 q = 1) (hb : d183716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182986, d183716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41280 q ha hb
    | true =>
      simp only [d182986, d183716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d182987 q = 1) (hb : d183717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182987, d183717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182987, d183717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d182993 q = 1) (hb : d183735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182993, d183735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182993, d183735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182994 q = 1) (hb : d183736 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182994, d183736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182994, d183736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182995 q = 1) (hb : d183737 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182995, d183737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182995, d183737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182996 q = 1) (hb : d183738 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182996, d183738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182996, d183738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41285 (p : Pattern) (ha : d183015 p = 1) (hb : d183744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183010 q = 1) (hb : d183739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183010, d183739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41284 q ha hb
    | true =>
      simp only [d183010, d183739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183011 q = 1) (hb : d183740 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183011, d183740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183011, d183740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183012 q = 1) (hb : d183741 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183012, d183741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183012, d183741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183013 q = 1) (hb : d183742 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183013, d183742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183013, d183742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183014 q = 1) (hb : d183743 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183014, d183743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183014, d183743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183015 q = 1) (hb : d183744 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183015, d183744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183015, d183744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41286 (p : Pattern) (ha : d183021 p = 1) (hb : d183750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183009 q = 1) (hb : d183734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183009, d183734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183009, d183734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41283 q ha hb
  have h2 (q : Pattern) (ha : d183016 q = 1) (hb : d183745 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183016, d183745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183016, d183745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41285 q ha hb
  have h3 (q : Pattern) (ha : d183017 q = 1) (hb : d183746 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d183017, d183746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183017, d183746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183018 q = 1) (hb : d183747 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d183018, d183747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183018, d183747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183019 q = 1) (hb : d183748 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d183019, d183748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183019, d183748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183020 q = 1) (hb : d183749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d183020, d183749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183020, d183749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183021 q = 1) (hb : d183750 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d183021, d183750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183021, d183750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41287 (p : Pattern) (ha : d183027 p = 1) (hb : d183756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183022 q = 1) (hb : d183751 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d183022, d183751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183022, d183751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41286 q ha hb
  have h2 (q : Pattern) (ha : d183023 q = 1) (hb : d183752 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d183023, d183752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183023, d183752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183024 q = 1) (hb : d183753 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d183024, d183753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183024, d183753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183025 q = 1) (hb : d183754 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d183025, d183754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183025, d183754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183026 q = 1) (hb : d183755 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d183026, d183755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183026, d183755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183027 q = 1) (hb : d183756 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d183027, d183756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183027, d183756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41288 (p : Pattern) (ha : d183037 p = 1) (hb : d183766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d52510 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9576 q = 1) (hb : d52510 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183029 q = 1) (hb : d183758 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183029, d183758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183029, d183758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183030 q = 1) (hb : d183759 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183030, d183759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183030, d183759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101166 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9587 q = 1) (hb : d101166 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23290 q ha hb
    | true =>
      simp only [d9587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9588 q = 1) (hb : d101166 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183031 q = 1) (hb : d183760 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183031, d183760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183031, d183760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183032 q = 1) (hb : d183761 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183032, d183761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183032, d183761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183033 q = 1) (hb : d183762 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183033, d183762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183033, d183762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101176 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9597 q = 1) (hb : d101176 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23291 q ha hb
    | true =>
      simp only [d9597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9598 q = 1) (hb : d101176 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183034 q = 1) (hb : d183763 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183034, d183763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d183034, d183763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d183035 q = 1) (hb : d183764 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183035, d183764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183035, d183764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d9468 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9469 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d182959 q = 1) (hb : d183689 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182959, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d182959, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h21 (q : Pattern) (ha : d182960 q = 1) (hb : d183690 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182960, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d182960, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h22 (q : Pattern) (ha : d183036 q = 1) (hb : d183765 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183036, d183765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d183036, d183765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d183037 q = 1) (hb : d183766 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183037, d183766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183037, d183766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41289 (p : Pattern) (ha : d183041 p = 1) (hb : d183770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52289 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d52289 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9449 q = 1) (hb : d52289 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d182954 q = 1) (hb : d183684 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182954, d183684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d182954, d183684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d182955 q = 1) (hb : d183685 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182955, d183685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182955, d183685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101072 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9458 q = 1) (hb : d101072 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
    | true =>
      simp only [d9458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9459 q = 1) (hb : d101072 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d182956 q = 1) (hb : d183686 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182956, d183686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d182956, d183686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d182957 q = 1) (hb : d183687 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182957, d183687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d182957, d183687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d182958 q = 1) (hb : d183688 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182958, d183688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182958, d183688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9468 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9469 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d182959 q = 1) (hb : d183689 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182959, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d182959, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d182960 q = 1) (hb : d183690 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182960, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d182960, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d751 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9604 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d183038 q = 1) (hb : d183767 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183038, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d183038, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h21 (q : Pattern) (ha : d183039 q = 1) (hb : d183768 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183039, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d183039, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h22 (q : Pattern) (ha : d183040 q = 1) (hb : d183769 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183040, d183769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d183040, d183769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d183041 q = 1) (hb : d183770 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183041, d183770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183041, d183770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41290 (p : Pattern) (ha : d183046 p = 1) (hb : d183775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9468 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9469 q = 1) (hb : d101082 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d182959 q = 1) (hb : d183689 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182959, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d182959, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d182960 q = 1) (hb : d183690 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182960, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182960, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d751 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9604 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183038 q = 1) (hb : d183767 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183038, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183038, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183039 q = 1) (hb : d183768 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183039, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183039, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183040 q = 1) (hb : d183769 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183040, d183769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183040, d183769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d183045 q = 1) (hb : d183774 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183045, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183045, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d183046 q = 1) (hb : d183775 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183046, d183775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183046, d183775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41291 (p : Pattern) (ha : d183052 p = 1) (hb : d183781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52117 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52117 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9377 q = 1) (hb : d52117 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d182905 q = 1) (hb : d183635 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182905, d183635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d182905, d183635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d182906 q = 1) (hb : d183636 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182906, d183636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182906, d183636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d751 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9604 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183038 q = 1) (hb : d183767 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183038, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183038, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183039 q = 1) (hb : d183768 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183039, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183039, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183051 q = 1) (hb : d183780 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183051, d183780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183051, d183780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d183045 q = 1) (hb : d183774 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183045, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183045, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d183052 q = 1) (hb : d183781 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183052, d183781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183052, d183781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41292 (p : Pattern) (ha : d183056 p = 1) (hb : d183785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9604 q = 1) (hb : d52427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183038 q = 1) (hb : d183767 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183038, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183038, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183039 q = 1) (hb : d183768 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183039, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183039, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d183045 q = 1) (hb : d183774 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183045, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183045, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d183056 q = 1) (hb : d183785 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183056, d183785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183056, d183785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h7 p ha hb
theorem andIntro41293 (p : Pattern) (ha : d183062 p = 1) (hb : d183791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183042 q = 1) (hb : d183771 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183042, d183771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41288 q ha hb
    | true =>
      simp only [d183042, d183771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41289 q ha hb
  have h2 (q : Pattern) (ha : d183043 q = 1) (hb : d183772 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183043, d183772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183043, d183772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183044 q = 1) (hb : d183773 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183044, d183773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183044, d183773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183047 q = 1) (hb : d183776 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183047, d183776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41289 q ha hb
    | true =>
      simp only [d183047, d183776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41290 q ha hb
  have h5 (q : Pattern) (ha : d183048 q = 1) (hb : d183777 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183048, d183777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183048, d183777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183049 q = 1) (hb : d183778 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183049, d183778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183049, d183778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183050 q = 1) (hb : d183779 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183050, d183779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183050, d183779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183053 q = 1) (hb : d183782 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183053, d183782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41289 q ha hb
    | true =>
      simp only [d183053, d183782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41291 q ha hb
  have h9 (q : Pattern) (ha : d183054 q = 1) (hb : d183783 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183054, d183783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183054, d183783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183055 q = 1) (hb : d183784 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183055, d183784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183055, d183784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183057 q = 1) (hb : d183786 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183057, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41291 q ha hb
    | true =>
      simp only [d183057, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41292 q ha hb
  have h12 (q : Pattern) (ha : d183058 q = 1) (hb : d183787 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183058, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183058, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183059 q = 1) (hb : d183788 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183059, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183059, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d183060 q = 1) (hb : d183789 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183060, d183789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183060, d183789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183061 q = 1) (hb : d183790 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183061, d183790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183061, d183790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d183062 q = 1) (hb : d183791 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183062, d183791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183062, d183791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro41294 (p : Pattern) (ha : d183067 p = 1) (hb : d183796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183053 q = 1) (hb : d183782 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183053, d183782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41289 q ha hb
    | true =>
      simp only [d183053, d183782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41291 q ha hb
  have h2 (q : Pattern) (ha : d183054 q = 1) (hb : d183783 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183054, d183783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183054, d183783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183055 q = 1) (hb : d183784 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183055, d183784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183055, d183784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183057 q = 1) (hb : d183786 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183057, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41291 q ha hb
    | true =>
      simp only [d183057, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41292 q ha hb
  have h5 (q : Pattern) (ha : d183058 q = 1) (hb : d183787 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183058, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183058, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183059 q = 1) (hb : d183788 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183059, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183059, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183060 q = 1) (hb : d183789 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183060, d183789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183060, d183789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183065 q = 1) (hb : d183794 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183065, d183794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183065, d183794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d183066 q = 1) (hb : d183795 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183066, d183795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183066, d183795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183067 q = 1) (hb : d183796 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183067, d183796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183067, d183796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro41295 (p : Pattern) (ha : d183073 p = 1) (hb : d183802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183063 q = 1) (hb : d183792 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183063, d183792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41293 q ha hb
    | true =>
      simp only [d183063, d183792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183064 q = 1) (hb : d183793 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183064, d183793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183064, d183793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183068 q = 1) (hb : d183797 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183068, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41294 q ha hb
    | true =>
      simp only [d183068, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183069 q = 1) (hb : d183798 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183069, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183069, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183070 q = 1) (hb : d183799 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183070, d183799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183070, d183799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183071 q = 1) (hb : d183800 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183071, d183800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183071, d183800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183072 q = 1) (hb : d183801 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183072, d183801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183072, d183801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d183073 q = 1) (hb : d183802 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183073, d183802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183073, d183802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41296 (p : Pattern) (ha : d183075 p = 1) (hb : d183804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183057 q = 1) (hb : d183786 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183057, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41291 q ha hb
    | true =>
      simp only [d183057, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41292 q ha hb
  have h2 (q : Pattern) (ha : d183058 q = 1) (hb : d183787 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183058, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183058, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183059 q = 1) (hb : d183788 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183059, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183059, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183065 q = 1) (hb : d183794 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183065, d183794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183065, d183794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183074 q = 1) (hb : d183803 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183074, d183803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183074, d183803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183075 q = 1) (hb : d183804 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183075, d183804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183075, d183804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41297 (p : Pattern) (ha : d183081 p = 1) (hb : d183810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183068 q = 1) (hb : d183797 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183068, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41294 q ha hb
    | true =>
      simp only [d183068, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183069 q = 1) (hb : d183798 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183069, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183069, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183076 q = 1) (hb : d183805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183076, d183805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41296 q ha hb
    | true =>
      simp only [d183076, d183805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183077 q = 1) (hb : d183806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183077, d183806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183077, d183806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183078 q = 1) (hb : d183807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183078, d183807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183078, d183807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183079 q = 1) (hb : d183808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183079, d183808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183079, d183808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183080 q = 1) (hb : d183809 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183080, d183809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183080, d183809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d183081 q = 1) (hb : d183810 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183081, d183810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183081, d183810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41298 (p : Pattern) (ha : d183092 p = 1) (hb : d183816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183068 q = 1) (hb : d183797 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183068, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41294 q ha hb
    | true =>
      simp only [d183068, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183069 q = 1) (hb : d183798 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183069, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183069, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183089 q = 1) (hb : d183813 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183089, d183813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183089, d183813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183090 q = 1) (hb : d183814 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183090, d183814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183090, d183814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183091 q = 1) (hb : d183815 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183091, d183815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183091, d183815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183092 q = 1) (hb : d183816 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183092, d183816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183092, d183816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41299 (p : Pattern) (ha : d183098 p = 1) (hb : d183822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183082 q = 1) (hb : d183811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183082, d183811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41295 q ha hb
    | true =>
      simp only [d183082, d183811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41297 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d183087 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d183088 q = 1) (hb : d183812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183088, d183812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183088, d183812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d183093 q = 1) (hb : d183817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183093, d183817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41298 q ha hb
    | true =>
      simp only [d183093, d183817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183094 q = 1) (hb : d183818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183094, d183818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183094, d183818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183095 q = 1) (hb : d183819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183095, d183819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183095, d183819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183096 q = 1) (hb : d183820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183096, d183820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183096, d183820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183097 q = 1) (hb : d183821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183097, d183821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183097, d183821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183098 q = 1) (hb : d183822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183098, d183822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183098, d183822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41300 (p : Pattern) (ha : d183086 p = 1) (hb : d183827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183076 q = 1) (hb : d183805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183076, d183805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41296 q ha hb
    | true =>
      simp only [d183076, d183805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183077 q = 1) (hb : d183806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183077, d183806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183077, d183806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183083 q = 1) (hb : d183824 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183083, d183824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183083, d183824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183084 q = 1) (hb : d183825 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183084, d183825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183084, d183825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183085 q = 1) (hb : d183826 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183085, d183826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183085, d183826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183086 q = 1) (hb : d183827 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183086, d183827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183086, d183827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41301 (p : Pattern) (ha : d183105 p = 1) (hb : d183833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183100 q = 1) (hb : d183828 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183100, d183828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41300 q ha hb
    | true =>
      simp only [d183100, d183828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183101 q = 1) (hb : d183829 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183101, d183829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183101, d183829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183102 q = 1) (hb : d183830 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183102, d183830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183102, d183830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183103 q = 1) (hb : d183831 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183103, d183831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183103, d183831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183104 q = 1) (hb : d183832 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183104, d183832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183104, d183832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183105 q = 1) (hb : d183833 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183105, d183833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183105, d183833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41302 (p : Pattern) (ha : d183111 p = 1) (hb : d183839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183099 q = 1) (hb : d183823 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183099, d183823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183099, d183823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41299 q ha hb
  have h2 (q : Pattern) (ha : d183106 q = 1) (hb : d183834 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183106, d183834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183106, d183834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41301 q ha hb
  have h3 (q : Pattern) (ha : d183107 q = 1) (hb : d183835 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d183107, d183835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183107, d183835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183108 q = 1) (hb : d183836 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d183108, d183836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183108, d183836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183109 q = 1) (hb : d183837 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d183109, d183837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183109, d183837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183110 q = 1) (hb : d183838 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d183110, d183838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183110, d183838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183111 q = 1) (hb : d183839 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d183111, d183839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183111, d183839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41303 (p : Pattern) (ha : d183117 p = 1) (hb : d183845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183112 q = 1) (hb : d183840 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d183112, d183840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183112, d183840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41302 q ha hb
  have h2 (q : Pattern) (ha : d183113 q = 1) (hb : d183841 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d183113, d183841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183113, d183841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183114 q = 1) (hb : d183842 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d183114, d183842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183114, d183842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183115 q = 1) (hb : d183843 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d183115, d183843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183115, d183843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183116 q = 1) (hb : d183844 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d183116, d183844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183116, d183844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183117 q = 1) (hb : d183845 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d183117, d183845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183117, d183845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41304 (p : Pattern) (ha : d183130 p = 1) (hb : d183858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52790 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d52790 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9746 q = 1) (hb : d52790 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183120 q = 1) (hb : d183848 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183120, d183848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183120, d183848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183121 q = 1) (hb : d183849 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183121, d183849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183121, d183849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101273 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9753 q = 1) (hb : d101273 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23310 q ha hb
    | true =>
      simp only [d9753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9754 q = 1) (hb : d101273 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183122 q = 1) (hb : d183850 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183122, d183850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183122, d183850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183123 q = 1) (hb : d183851 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183123, d183851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183123, d183851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183124 q = 1) (hb : d183852 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183124, d183852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183124, d183852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101283 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9763 q = 1) (hb : d101283 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23311 q ha hb
    | true =>
      simp only [d9763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9764 q = 1) (hb : d101283 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183125 q = 1) (hb : d183853 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183125, d183853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d183125, d183853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d183126 q = 1) (hb : d183854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183126, d183854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183126, d183854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101298 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d9778 q = 1) (hb : d101298 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
    | true =>
      simp only [d9778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9779 q = 1) (hb : d101298 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d183127 q = 1) (hb : d183855 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183127, d183855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d183127, d183855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h21 (q : Pattern) (ha : d183128 q = 1) (hb : d183856 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183128, d183856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d183128, d183856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h22 (q : Pattern) (ha : d183129 q = 1) (hb : d183857 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183129, d183857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d183129, d183857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d183130 q = 1) (hb : d183858 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183130, d183858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183130, d183858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41305 (p : Pattern) (ha : d183139 p = 1) (hb : d183867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52680 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d52680 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9785 q = 1) (hb : d52680 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183131 q = 1) (hb : d183859 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183131, d183859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183131, d183859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183132 q = 1) (hb : d183860 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183132, d183860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183132, d183860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101309 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9789 q = 1) (hb : d101309 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23315 q ha hb
    | true =>
      simp only [d9789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9790 q = 1) (hb : d101309 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183133 q = 1) (hb : d183861 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183133, d183861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183133, d183861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183134 q = 1) (hb : d183862 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183134, d183862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183134, d183862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183135 q = 1) (hb : d183863 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183135, d183863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183135, d183863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101298 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9778 q = 1) (hb : d101298 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
    | true =>
      simp only [d9778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9779 q = 1) (hb : d101298 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183127 q = 1) (hb : d183855 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183127, d183855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d183127, d183855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d183128 q = 1) (hb : d183856 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183128, d183856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183128, d183856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101320 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d9800 q = 1) (hb : d101320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9801 q = 1) (hb : d101320 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d183136 q = 1) (hb : d183864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183136, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d183136, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h21 (q : Pattern) (ha : d183137 q = 1) (hb : d183865 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183137, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d183137, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h22 (q : Pattern) (ha : d183138 q = 1) (hb : d183866 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183138, d183866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d183138, d183866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d183139 q = 1) (hb : d183867 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183139, d183867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183139, d183867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41306 (p : Pattern) (ha : d183147 p = 1) (hb : d183875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9814 q = 1) (hb : d101334 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23317 q ha hb
    | true =>
      simp only [d9814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9815 q = 1) (hb : d101334 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183143 q = 1) (hb : d183871 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183143, d183871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183143, d183871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183144 q = 1) (hb : d183872 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183144, d183872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183144, d183872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101320 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9800 q = 1) (hb : d101320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9801 q = 1) (hb : d101320 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183136 q = 1) (hb : d183864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183136, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183136, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183137 q = 1) (hb : d183865 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183137, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183137, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183145 q = 1) (hb : d183873 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183145, d183873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183145, d183873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d183146 q = 1) (hb : d183874 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183146, d183874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183146, d183874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d183147 q = 1) (hb : d183875 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183147, d183875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183147, d183875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41307 (p : Pattern) (ha : d183157 p = 1) (hb : d183885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52690 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d52690 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9826 q = 1) (hb : d52690 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183152 q = 1) (hb : d183880 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183152, d183880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183152, d183880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183153 q = 1) (hb : d183881 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183153, d183881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183153, d183881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1121 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9829 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183154 q = 1) (hb : d183882 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183154, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183154, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183155 q = 1) (hb : d183883 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183155, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183155, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183156 q = 1) (hb : d183884 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183156, d183884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183156, d183884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101320 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9800 q = 1) (hb : d101320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9801 q = 1) (hb : d101320 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183136 q = 1) (hb : d183864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183136, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d183136, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d183137 q = 1) (hb : d183865 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183137, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183137, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d183146 q = 1) (hb : d183874 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183146, d183874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d183146, d183874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h18 (q : Pattern) (ha : d183157 q = 1) (hb : d183885 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183157, d183885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183157, d183885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro41308 (p : Pattern) (ha : d183167 p = 1) (hb : d183895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69107 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5018 q = 1) (hb : d69107 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
    | true =>
      simp only [d5018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9837 q = 1) (hb : d69107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183161 q = 1) (hb : d183889 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183161, d183889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183161, d183889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183162 q = 1) (hb : d183890 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183162, d183890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183162, d183890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d183163 q = 1) (hb : d183891 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183163, d183891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183163, d183891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101364 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9844 q = 1) (hb : d101364 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9845 q = 1) (hb : d101364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183164 q = 1) (hb : d183892 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183164, d183892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d183164, d183892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183165 q = 1) (hb : d183893 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183165, d183893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183165, d183893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d183166 q = 1) (hb : d183894 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183166, d183894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183166, d183894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d183167 q = 1) (hb : d183895 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183167, d183895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183167, d183895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41309 (p : Pattern) (ha : d183173 p = 1) (hb : d183901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183140 q = 1) (hb : d183868 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183140, d183868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41304 q ha hb
    | true =>
      simp only [d183140, d183868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41305 q ha hb
  have h2 (q : Pattern) (ha : d183141 q = 1) (hb : d183869 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183141, d183869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183141, d183869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183142 q = 1) (hb : d183870 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183142, d183870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183142, d183870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183148 q = 1) (hb : d183876 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183148, d183876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41305 q ha hb
    | true =>
      simp only [d183148, d183876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41306 q ha hb
  have h5 (q : Pattern) (ha : d183149 q = 1) (hb : d183877 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183149, d183877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183149, d183877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183150 q = 1) (hb : d183878 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183150, d183878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183150, d183878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183151 q = 1) (hb : d183879 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183151, d183879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183151, d183879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183158 q = 1) (hb : d183886 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183158, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41305 q ha hb
    | true =>
      simp only [d183158, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41307 q ha hb
  have h9 (q : Pattern) (ha : d183159 q = 1) (hb : d183887 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183159, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183159, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183160 q = 1) (hb : d183888 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183160, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183160, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183168 q = 1) (hb : d183896 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183168, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41307 q ha hb
    | true =>
      simp only [d183168, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41308 q ha hb
  have h12 (q : Pattern) (ha : d183169 q = 1) (hb : d183897 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183169, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183169, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183170 q = 1) (hb : d183898 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183170, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183170, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d183171 q = 1) (hb : d183899 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183171, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183171, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183172 q = 1) (hb : d183900 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183172, d183900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183172, d183900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d183173 q = 1) (hb : d183901 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183173, d183901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183173, d183901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro41310 (p : Pattern) (ha : d183178 p = 1) (hb : d183906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183158 q = 1) (hb : d183886 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183158, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41305 q ha hb
    | true =>
      simp only [d183158, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41307 q ha hb
  have h2 (q : Pattern) (ha : d183159 q = 1) (hb : d183887 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183159, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183159, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183160 q = 1) (hb : d183888 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183160, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183160, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183168 q = 1) (hb : d183896 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183168, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41307 q ha hb
    | true =>
      simp only [d183168, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41308 q ha hb
  have h5 (q : Pattern) (ha : d183169 q = 1) (hb : d183897 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183169, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183169, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183170 q = 1) (hb : d183898 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183170, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183170, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183171 q = 1) (hb : d183899 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183171, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183171, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183176 q = 1) (hb : d183904 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183176, d183904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183176, d183904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d183177 q = 1) (hb : d183905 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183177, d183905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183177, d183905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183178 q = 1) (hb : d183906 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183178, d183906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183178, d183906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro41311 (p : Pattern) (ha : d183184 p = 1) (hb : d183912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183174 q = 1) (hb : d183902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183174, d183902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41309 q ha hb
    | true =>
      simp only [d183174, d183902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183175 q = 1) (hb : d183903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183175, d183903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183175, d183903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183179 q = 1) (hb : d183907 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183179, d183907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41310 q ha hb
    | true =>
      simp only [d183179, d183907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183180 q = 1) (hb : d183908 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183180, d183908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183180, d183908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183181 q = 1) (hb : d183909 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183181, d183909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183181, d183909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183182 q = 1) (hb : d183910 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183182, d183910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183182, d183910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183183 q = 1) (hb : d183911 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183183, d183911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183183, d183911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d183184 q = 1) (hb : d183912 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183184, d183912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183184, d183912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41312 (p : Pattern) (ha : d183186 p = 1) (hb : d183914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9829 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183154 q = 1) (hb : d183882 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183154, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183154, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183155 q = 1) (hb : d183883 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183155, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183155, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d183185 q = 1) (hb : d183913 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183185, d183913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183185, d183913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101364 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9844 q = 1) (hb : d101364 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9845 q = 1) (hb : d101364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183164 q = 1) (hb : d183892 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183164, d183892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d183164, d183892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183165 q = 1) (hb : d183893 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183165, d183893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183165, d183893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d183166 q = 1) (hb : d183894 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183166, d183894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183166, d183894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d183186 q = 1) (hb : d183914 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183186, d183914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183186, d183914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41313 (p : Pattern) (ha : d183192 p = 1) (hb : d183920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183187 q = 1) (hb : d183915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183187, d183915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41307 q ha hb
    | true =>
      simp only [d183187, d183915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41312 q ha hb
  have h2 (q : Pattern) (ha : d183188 q = 1) (hb : d183916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183188, d183916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183188, d183916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183189 q = 1) (hb : d183917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183189, d183917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183189, d183917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183190 q = 1) (hb : d183918 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183190, d183918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183190, d183918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183191 q = 1) (hb : d183919 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183191, d183919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183191, d183919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183192 q = 1) (hb : d183920 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183192, d183920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183192, d183920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41314 (p : Pattern) (ha : d183198 p = 1) (hb : d183926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183179 q = 1) (hb : d183907 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183179, d183907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41310 q ha hb
    | true =>
      simp only [d183179, d183907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183180 q = 1) (hb : d183908 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183180, d183908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183180, d183908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183193 q = 1) (hb : d183921 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183193, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41313 q ha hb
    | true =>
      simp only [d183193, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183194 q = 1) (hb : d183922 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183194, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183194, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183195 q = 1) (hb : d183923 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183195, d183923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183195, d183923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183196 q = 1) (hb : d183924 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183196, d183924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183196, d183924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183197 q = 1) (hb : d183925 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183197, d183925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183197, d183925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d183198 q = 1) (hb : d183926 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183198, d183926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183198, d183926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41315 (p : Pattern) (ha : d183214 p = 1) (hb : d183929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9829 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183154 q = 1) (hb : d183882 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183154, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183154, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183155 q = 1) (hb : d183883 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183155, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183155, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d183185 q = 1) (hb : d183913 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183185, d183913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183185, d183913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d183214 q = 1) (hb : d183929 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183214, d183929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183214, d183929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h7 p ha hb
theorem andIntro41316 (p : Pattern) (ha : d183220 p = 1) (hb : d183935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183158 q = 1) (hb : d183886 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183158, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41305 q ha hb
    | true =>
      simp only [d183158, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41307 q ha hb
  have h2 (q : Pattern) (ha : d183159 q = 1) (hb : d183887 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183159, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183159, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183160 q = 1) (hb : d183888 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183160, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183160, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183168 q = 1) (hb : d183896 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183168, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41307 q ha hb
    | true =>
      simp only [d183168, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41308 q ha hb
  have h5 (q : Pattern) (ha : d183169 q = 1) (hb : d183897 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183169, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183169, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183170 q = 1) (hb : d183898 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183170, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183170, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183171 q = 1) (hb : d183899 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183171, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183171, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183215 q = 1) (hb : d183930 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183215, d183930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41307 q ha hb
    | true =>
      simp only [d183215, d183930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41315 q ha hb
  have h9 (q : Pattern) (ha : d183216 q = 1) (hb : d183931 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183216, d183931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183216, d183931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183217 q = 1) (hb : d183932 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183217, d183932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183217, d183932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183218 q = 1) (hb : d183933 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183218, d183933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183218, d183933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d183219 q = 1) (hb : d183934 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183219, d183934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183219, d183934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183220 q = 1) (hb : d183935 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183220, d183935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d183220, d183935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41317 (p : Pattern) (ha : d183226 p = 1) (hb : d183941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183221 q = 1) (hb : d183936 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183221, d183936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41316 q ha hb
    | true =>
      simp only [d183221, d183936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183222 q = 1) (hb : d183937 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183222, d183937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183222, d183937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183223 q = 1) (hb : d183938 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183223, d183938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183223, d183938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183224 q = 1) (hb : d183939 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183224, d183939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183224, d183939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183225 q = 1) (hb : d183940 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183225, d183940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183225, d183940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183226 q = 1) (hb : d183941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183226, d183941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183226, d183941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41318 (p : Pattern) (ha : d183232 p = 1) (hb : d183947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183199 q = 1) (hb : d183927 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183199, d183927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41311 q ha hb
    | true =>
      simp only [d183199, d183927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41314 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d183212 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d183213 q = 1) (hb : d183928 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183213, d183928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183213, d183928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d183227 q = 1) (hb : d183942 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183227, d183942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41317 q ha hb
    | true =>
      simp only [d183227, d183942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183228 q = 1) (hb : d183943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183228, d183943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183228, d183943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183229 q = 1) (hb : d183944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183229, d183944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183229, d183944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183230 q = 1) (hb : d183945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183230, d183945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183230, d183945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183231 q = 1) (hb : d183946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183231, d183946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183231, d183946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183232 q = 1) (hb : d183947 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183232, d183947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183232, d183947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41319 (p : Pattern) (ha : d183211 p = 1) (hb : d183952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183193 q = 1) (hb : d183921 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183193, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41313 q ha hb
    | true =>
      simp only [d183193, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183194 q = 1) (hb : d183922 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183194, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183194, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183208 q = 1) (hb : d183949 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183208, d183949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183208, d183949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183209 q = 1) (hb : d183950 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183209, d183950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183209, d183950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183210 q = 1) (hb : d183951 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183210, d183951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183210, d183951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183211 q = 1) (hb : d183952 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183211, d183952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183211, d183952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41320 (p : Pattern) (ha : d183239 p = 1) (hb : d183958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183234 q = 1) (hb : d183953 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183234, d183953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41319 q ha hb
    | true =>
      simp only [d183234, d183953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183235 q = 1) (hb : d183954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183235, d183954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183235, d183954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183236 q = 1) (hb : d183955 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183236, d183955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183236, d183955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183237 q = 1) (hb : d183956 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183237, d183956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183237, d183956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183238 q = 1) (hb : d183957 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183238, d183957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183238, d183957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183239 q = 1) (hb : d183958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183239, d183958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183239, d183958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41321 (p : Pattern) (ha : d183245 p = 1) (hb : d183964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183233 q = 1) (hb : d183948 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183233, d183948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183233, d183948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41318 q ha hb
  have h2 (q : Pattern) (ha : d183240 q = 1) (hb : d183959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183240, d183959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183240, d183959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41320 q ha hb
  have h3 (q : Pattern) (ha : d183241 q = 1) (hb : d183960 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d183241, d183960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183241, d183960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183242 q = 1) (hb : d183961 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d183242, d183961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183242, d183961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183243 q = 1) (hb : d183962 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d183243, d183962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183243, d183962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183244 q = 1) (hb : d183963 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d183244, d183963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183244, d183963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183245 q = 1) (hb : d183964 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d183245, d183964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183245, d183964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41322 (p : Pattern) (ha : d183251 p = 1) (hb : d183970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183246 q = 1) (hb : d183965 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d183246, d183965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183246, d183965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41321 q ha hb
  have h2 (q : Pattern) (ha : d183247 q = 1) (hb : d183966 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d183247, d183966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183247, d183966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183248 q = 1) (hb : d183967 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d183248, d183967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183248, d183967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183249 q = 1) (hb : d183968 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d183249, d183968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183249, d183968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183250 q = 1) (hb : d183969 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d183250, d183969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183250, d183969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183251 q = 1) (hb : d183970 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d183251, d183970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183251, d183970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41323 (p : Pattern) (ha : d183265 p = 1) (hb : d183984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53105 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d53105 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10032 q = 1) (hb : d53105 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183255 q = 1) (hb : d183974 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183255, d183974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183255, d183974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183256 q = 1) (hb : d183975 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183256, d183975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183256, d183975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101462 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10036 q = 1) (hb : d101462 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
    | true =>
      simp only [d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10037 q = 1) (hb : d101462 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183257 q = 1) (hb : d183976 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183257, d183976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183257, d183976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183258 q = 1) (hb : d183977 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183258, d183977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183258, d183977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183259 q = 1) (hb : d183978 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183259, d183978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183259, d183978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101472 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10046 q = 1) (hb : d101472 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
    | true =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10047 q = 1) (hb : d101472 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183260 q = 1) (hb : d183979 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183260, d183979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d183260, d183979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d183261 q = 1) (hb : d183980 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183261, d183980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183261, d183980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101489 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10063 q = 1) (hb : d101489 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
    | true =>
      simp only [d10063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10064 q = 1) (hb : d101489 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d183262 q = 1) (hb : d183981 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183262, d183981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d183262, d183981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h21 (q : Pattern) (ha : d183263 q = 1) (hb : d183982 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183263, d183982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d183263, d183982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h22 (q : Pattern) (ha : d183264 q = 1) (hb : d183983 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183264, d183983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d183264, d183983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d183265 q = 1) (hb : d183984 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183265, d183984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183265, d183984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41324 (p : Pattern) (ha : d183274 p = 1) (hb : d183993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52995 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d52995 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10070 q = 1) (hb : d52995 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183266 q = 1) (hb : d183985 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183266, d183985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183266, d183985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183267 q = 1) (hb : d183986 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183267, d183986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183267, d183986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101500 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10074 q = 1) (hb : d101500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23343 q ha hb
    | true =>
      simp only [d10074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10075 q = 1) (hb : d101500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183268 q = 1) (hb : d183987 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183268, d183987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183268, d183987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183269 q = 1) (hb : d183988 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183269, d183988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183269, d183988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183270 q = 1) (hb : d183989 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183270, d183989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183270, d183989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101489 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10063 q = 1) (hb : d101489 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
    | true =>
      simp only [d10063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10064 q = 1) (hb : d101489 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183262 q = 1) (hb : d183981 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183262, d183981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d183262, d183981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d183263 q = 1) (hb : d183982 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183263, d183982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183263, d183982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101511 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10085 q = 1) (hb : d101511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10086 q = 1) (hb : d101511 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d183271 q = 1) (hb : d183990 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183271, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d183271, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h21 (q : Pattern) (ha : d183272 q = 1) (hb : d183991 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183272, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d183272, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h22 (q : Pattern) (ha : d183273 q = 1) (hb : d183992 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183273, d183992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d183273, d183992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d183274 q = 1) (hb : d183993 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183274, d183993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183274, d183993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41325 (p : Pattern) (ha : d183282 p = 1) (hb : d184001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101525 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10099 q = 1) (hb : d101525 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
    | true =>
      simp only [d10099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10100 q = 1) (hb : d101525 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183278 q = 1) (hb : d183997 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183278, d183997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183278, d183997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183279 q = 1) (hb : d183998 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183279, d183998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183279, d183998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101511 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10085 q = 1) (hb : d101511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10086 q = 1) (hb : d101511 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183271 q = 1) (hb : d183990 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183271, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183271, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183272 q = 1) (hb : d183991 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183272, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183272, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183280 q = 1) (hb : d183999 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183280, d183999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183280, d183999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d183281 q = 1) (hb : d184000 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183281, d184000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183281, d184000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d183282 q = 1) (hb : d184001 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183282, d184001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183282, d184001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41326 (p : Pattern) (ha : d183292 p = 1) (hb : d184011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53010 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d53010 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10111 q = 1) (hb : d53010 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183287 q = 1) (hb : d184006 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183287, d184006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183287, d184006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183288 q = 1) (hb : d184007 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183288, d184007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183288, d184007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101541 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10115 q = 1) (hb : d101541 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23331 q ha hb
    | true =>
      simp only [d10115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10116 q = 1) (hb : d101541 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183289 q = 1) (hb : d184008 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183289, d184008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183289, d184008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183290 q = 1) (hb : d184009 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183290, d184009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183290, d184009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183291 q = 1) (hb : d184010 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183291, d184010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183291, d184010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101511 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10085 q = 1) (hb : d101511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10086 q = 1) (hb : d101511 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183271 q = 1) (hb : d183990 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183271, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d183271, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d183272 q = 1) (hb : d183991 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183272, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183272, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d183281 q = 1) (hb : d184000 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183281, d184000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d183281, d184000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h18 (q : Pattern) (ha : d183292 q = 1) (hb : d184011 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183292, d184011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183292, d184011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro41327 (p : Pattern) (ha : d183302 p = 1) (hb : d184021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69220 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5134 q = 1) (hb : d69220 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
    | true =>
      simp only [d5134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10125 q = 1) (hb : d69220 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183296 q = 1) (hb : d184015 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183296, d184015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183296, d184015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183297 q = 1) (hb : d184016 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183297, d184016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183297, d184016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d183298 q = 1) (hb : d184017 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183298, d184017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183298, d184017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101561 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10135 q = 1) (hb : d101561 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10136 q = 1) (hb : d101561 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183299 q = 1) (hb : d184018 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183299, d184018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d183299, d184018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183300 q = 1) (hb : d184019 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183300, d184019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183300, d184019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d183301 q = 1) (hb : d184020 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183301, d184020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183301, d184020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d183302 q = 1) (hb : d184021 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183302, d184021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183302, d184021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41328 (p : Pattern) (ha : d183308 p = 1) (hb : d184027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183275 q = 1) (hb : d183994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183275, d183994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41323 q ha hb
    | true =>
      simp only [d183275, d183994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41324 q ha hb
  have h2 (q : Pattern) (ha : d183276 q = 1) (hb : d183995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183276, d183995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183276, d183995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183277 q = 1) (hb : d183996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183277, d183996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183277, d183996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183283 q = 1) (hb : d184002 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183283, d184002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41324 q ha hb
    | true =>
      simp only [d183283, d184002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41325 q ha hb
  have h5 (q : Pattern) (ha : d183284 q = 1) (hb : d184003 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183284, d184003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183284, d184003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183285 q = 1) (hb : d184004 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183285, d184004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183285, d184004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183286 q = 1) (hb : d184005 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183286, d184005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183286, d184005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183293 q = 1) (hb : d184012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183293, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41324 q ha hb
    | true =>
      simp only [d183293, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41326 q ha hb
  have h9 (q : Pattern) (ha : d183294 q = 1) (hb : d184013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183294, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183294, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183295 q = 1) (hb : d184014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183295, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183295, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183303 q = 1) (hb : d184022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183303, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41326 q ha hb
    | true =>
      simp only [d183303, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41327 q ha hb
  have h12 (q : Pattern) (ha : d183304 q = 1) (hb : d184023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183304, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183304, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183305 q = 1) (hb : d184024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183305, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183305, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d183306 q = 1) (hb : d184025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183306, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183306, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183307 q = 1) (hb : d184026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183307, d184026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183307, d184026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d183308 q = 1) (hb : d184027 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183308, d184027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183308, d184027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro41329 (p : Pattern) (ha : d183313 p = 1) (hb : d184032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183293 q = 1) (hb : d184012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183293, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41324 q ha hb
    | true =>
      simp only [d183293, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41326 q ha hb
  have h2 (q : Pattern) (ha : d183294 q = 1) (hb : d184013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183294, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183294, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183295 q = 1) (hb : d184014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183295, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183295, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183303 q = 1) (hb : d184022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183303, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41326 q ha hb
    | true =>
      simp only [d183303, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41327 q ha hb
  have h5 (q : Pattern) (ha : d183304 q = 1) (hb : d184023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183304, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183304, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183305 q = 1) (hb : d184024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183305, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183305, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183306 q = 1) (hb : d184025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183306, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183306, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183311 q = 1) (hb : d184030 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183311, d184030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183311, d184030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d183312 q = 1) (hb : d184031 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183312, d184031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183312, d184031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183313 q = 1) (hb : d184032 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183313, d184032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183313, d184032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro41330 (p : Pattern) (ha : d183319 p = 1) (hb : d184038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183309 q = 1) (hb : d184028 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183309, d184028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41328 q ha hb
    | true =>
      simp only [d183309, d184028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183310 q = 1) (hb : d184029 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183310, d184029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183310, d184029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183314 q = 1) (hb : d184033 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183314, d184033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41329 q ha hb
    | true =>
      simp only [d183314, d184033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183315 q = 1) (hb : d184034 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183315, d184034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183315, d184034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183316 q = 1) (hb : d184035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183316, d184035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183316, d184035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183317 q = 1) (hb : d184036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183317, d184036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183317, d184036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183318 q = 1) (hb : d184037 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183318, d184037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183318, d184037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d183319 q = 1) (hb : d184038 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183319, d184038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183319, d184038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41331 (p : Pattern) (ha : d183323 p = 1) (hb : d184042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d53022 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10159 q = 1) (hb : d53022 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183320 q = 1) (hb : d184039 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183320, d184039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183320, d184039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183321 q = 1) (hb : d184040 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183321, d184040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183321, d184040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d183322 q = 1) (hb : d184041 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183322, d184041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183322, d184041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101561 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10135 q = 1) (hb : d101561 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10136 q = 1) (hb : d101561 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183299 q = 1) (hb : d184018 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183299, d184018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d183299, d184018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183300 q = 1) (hb : d184019 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183300, d184019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183300, d184019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d183301 q = 1) (hb : d184020 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183301, d184020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183301, d184020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d183323 q = 1) (hb : d184042 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183323, d184042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183323, d184042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41332 (p : Pattern) (ha : d183329 p = 1) (hb : d184048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183324 q = 1) (hb : d184043 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183324, d184043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41326 q ha hb
    | true =>
      simp only [d183324, d184043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41331 q ha hb
  have h2 (q : Pattern) (ha : d183325 q = 1) (hb : d184044 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183325, d184044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183325, d184044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183326 q = 1) (hb : d184045 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183326, d184045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183326, d184045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183327 q = 1) (hb : d184046 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183327, d184046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183327, d184046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183328 q = 1) (hb : d184047 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183328, d184047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183328, d184047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183329 q = 1) (hb : d184048 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183329, d184048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183329, d184048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41333 (p : Pattern) (ha : d183335 p = 1) (hb : d184054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183314 q = 1) (hb : d184033 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183314, d184033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41329 q ha hb
    | true =>
      simp only [d183314, d184033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183315 q = 1) (hb : d184034 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183315, d184034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183315, d184034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183330 q = 1) (hb : d184049 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183330, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41332 q ha hb
    | true =>
      simp only [d183330, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183331 q = 1) (hb : d184050 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183331, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183331, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183332 q = 1) (hb : d184051 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183332, d184051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183332, d184051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183333 q = 1) (hb : d184052 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183333, d184052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183333, d184052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183334 q = 1) (hb : d184053 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183334, d184053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183334, d184053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d183335 q = 1) (hb : d184054 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183335, d184054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183335, d184054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41334 (p : Pattern) (ha : d183351 p = 1) (hb : d184057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d53022 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10159 q = 1) (hb : d53022 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183320 q = 1) (hb : d184039 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183320, d184039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183320, d184039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183321 q = 1) (hb : d184040 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183321, d184040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183321, d184040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d183322 q = 1) (hb : d184041 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183322, d184041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183322, d184041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d183351 q = 1) (hb : d184057 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183351, d184057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183351, d184057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h7 p ha hb
theorem andIntro41335 (p : Pattern) (ha : d183357 p = 1) (hb : d184063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183293 q = 1) (hb : d184012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183293, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41324 q ha hb
    | true =>
      simp only [d183293, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41326 q ha hb
  have h2 (q : Pattern) (ha : d183294 q = 1) (hb : d184013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183294, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183294, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183295 q = 1) (hb : d184014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183295, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183295, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183303 q = 1) (hb : d184022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183303, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41326 q ha hb
    | true =>
      simp only [d183303, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41327 q ha hb
  have h5 (q : Pattern) (ha : d183304 q = 1) (hb : d184023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183304, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183304, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183305 q = 1) (hb : d184024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183305, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183305, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183306 q = 1) (hb : d184025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183306, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183306, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183352 q = 1) (hb : d184058 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183352, d184058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41326 q ha hb
    | true =>
      simp only [d183352, d184058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41334 q ha hb
  have h9 (q : Pattern) (ha : d183353 q = 1) (hb : d184059 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183353, d184059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183353, d184059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183354 q = 1) (hb : d184060 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183354, d184060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183354, d184060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183355 q = 1) (hb : d184061 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183355, d184061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183355, d184061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d183356 q = 1) (hb : d184062 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183356, d184062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183356, d184062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183357 q = 1) (hb : d184063 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183357, d184063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d183357, d184063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41336 (p : Pattern) (ha : d183363 p = 1) (hb : d184069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183358 q = 1) (hb : d184064 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183358, d184064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41335 q ha hb
    | true =>
      simp only [d183358, d184064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183359 q = 1) (hb : d184065 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183359, d184065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183359, d184065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183360 q = 1) (hb : d184066 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183360, d184066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183360, d184066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183361 q = 1) (hb : d184067 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183361, d184067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183361, d184067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183362 q = 1) (hb : d184068 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183362, d184068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183362, d184068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183363 q = 1) (hb : d184069 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183363, d184069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183363, d184069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41337 (p : Pattern) (ha : d183369 p = 1) (hb : d184075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183336 q = 1) (hb : d184055 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183336, d184055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41330 q ha hb
    | true =>
      simp only [d183336, d184055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41333 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d183349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d183350 q = 1) (hb : d184056 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183350, d184056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183350, d184056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d183364 q = 1) (hb : d184070 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183364, d184070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41336 q ha hb
    | true =>
      simp only [d183364, d184070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183365 q = 1) (hb : d184071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183365, d184071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183365, d184071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183366 q = 1) (hb : d184072 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183366, d184072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183366, d184072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183367 q = 1) (hb : d184073 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183367, d184073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183367, d184073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183368 q = 1) (hb : d184074 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183368, d184074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183368, d184074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183369 q = 1) (hb : d184075 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183369, d184075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183369, d184075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41338 (p : Pattern) (ha : d183348 p = 1) (hb : d184080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183330 q = 1) (hb : d184049 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183330, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41332 q ha hb
    | true =>
      simp only [d183330, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183331 q = 1) (hb : d184050 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183331, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183331, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183345 q = 1) (hb : d184077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183345, d184077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183345, d184077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183346 q = 1) (hb : d184078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183346, d184078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183346, d184078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183347 q = 1) (hb : d184079 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183347, d184079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183347, d184079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183348 q = 1) (hb : d184080 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183348, d184080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183348, d184080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41339 (p : Pattern) (ha : d183376 p = 1) (hb : d184086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183371 q = 1) (hb : d184081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183371, d184081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41338 q ha hb
    | true =>
      simp only [d183371, d184081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183372 q = 1) (hb : d184082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183372, d184082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183372, d184082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183373 q = 1) (hb : d184083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183373, d184083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183373, d184083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183374 q = 1) (hb : d184084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183374, d184084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183374, d184084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183375 q = 1) (hb : d184085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183375, d184085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183375, d184085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183376 q = 1) (hb : d184086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183376, d184086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183376, d184086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41340 (p : Pattern) (ha : d183382 p = 1) (hb : d184092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183370 q = 1) (hb : d184076 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183370, d184076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183370, d184076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41337 q ha hb
  have h2 (q : Pattern) (ha : d183377 q = 1) (hb : d184087 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183377, d184087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183377, d184087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41339 q ha hb
  have h3 (q : Pattern) (ha : d183378 q = 1) (hb : d184088 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d183378, d184088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183378, d184088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183379 q = 1) (hb : d184089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d183379, d184089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183379, d184089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183380 q = 1) (hb : d184090 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d183380, d184090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183380, d184090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183381 q = 1) (hb : d184091 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d183381, d184091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183381, d184091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183382 q = 1) (hb : d184092 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d183382, d184092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183382, d184092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41341 (p : Pattern) (ha : d183388 p = 1) (hb : d184098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183383 q = 1) (hb : d184093 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d183383, d184093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183383, d184093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41340 q ha hb
  have h2 (q : Pattern) (ha : d183384 q = 1) (hb : d184094 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d183384, d184094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183384, d184094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183385 q = 1) (hb : d184095 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d183385, d184095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183385, d184095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183386 q = 1) (hb : d184096 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d183386, d184096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183386, d184096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183387 q = 1) (hb : d184097 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d183387, d184097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183387, d184097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183388 q = 1) (hb : d184098 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d183388, d184098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183388, d184098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41342 (p : Pattern) (ha : d183401 p = 1) (hb : d184111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53422 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2144 q = 1) (hb : d53422 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10339 q = 1) (hb : d53422 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183393 q = 1) (hb : d184103 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183393, d184103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183393, d184103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183394 q = 1) (hb : d184104 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183394, d184104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183394, d184104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101663 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10343 q = 1) (hb : d101663 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10344 q = 1) (hb : d101663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183395 q = 1) (hb : d184105 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183395, d184105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183395, d184105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183396 q = 1) (hb : d184106 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183396, d184106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183396, d184106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183397 q = 1) (hb : d184107 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183397, d184107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183397, d184107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101673 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10353 q = 1) (hb : d101673 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10354 q = 1) (hb : d101673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183398 q = 1) (hb : d184108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183398, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d183398, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d183399 q = 1) (hb : d184109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183399, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183399, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d183400 q = 1) (hb : d184110 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183400, d184110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d183400, d184110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d183401 q = 1) (hb : d184111 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183401, d184111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183401, d184111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro41343 (p : Pattern) (ha : d183410 p = 1) (hb : d184120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2035 q = 1) (hb : d53313 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10360 q = 1) (hb : d53313 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183402 q = 1) (hb : d184112 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183402, d184112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183402, d184112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183403 q = 1) (hb : d184113 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183403, d184113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183403, d184113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101684 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10364 q = 1) (hb : d101684 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10365 q = 1) (hb : d101684 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183404 q = 1) (hb : d184114 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183404, d184114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183404, d184114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183405 q = 1) (hb : d184115 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183405, d184115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183405, d184115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183406 q = 1) (hb : d184116 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183406, d184116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183406, d184116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101673 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10353 q = 1) (hb : d101673 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10354 q = 1) (hb : d101673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183398 q = 1) (hb : d184108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183398, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d183398, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d183399 q = 1) (hb : d184109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183399, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183399, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101691 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10371 q = 1) (hb : d101691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10372 q = 1) (hb : d101691 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d183407 q = 1) (hb : d184117 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183407, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d183407, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h21 (q : Pattern) (ha : d183408 q = 1) (hb : d184118 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183408, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d183408, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h22 (q : Pattern) (ha : d183409 q = 1) (hb : d184119 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183409, d184119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d183409, d184119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d183410 q = 1) (hb : d184120 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183410, d184120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183410, d184120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41344 (p : Pattern) (ha : d183415 p = 1) (hb : d184125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101673 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d101673 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10354 q = 1) (hb : d101673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183398 q = 1) (hb : d184108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183398, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183398, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183399 q = 1) (hb : d184109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183399, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183399, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101691 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10371 q = 1) (hb : d101691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10372 q = 1) (hb : d101691 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183407 q = 1) (hb : d184117 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183407, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183407, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183408 q = 1) (hb : d184118 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183408, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183408, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183409 q = 1) (hb : d184119 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183409, d184119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183409, d184119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d183414 q = 1) (hb : d184124 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183414, d184124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183414, d184124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d183415 q = 1) (hb : d184125 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183415, d184125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183415, d184125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41345 (p : Pattern) (ha : d183425 p = 1) (hb : d184135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53331 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2053 q = 1) (hb : d53331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10387 q = 1) (hb : d53331 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183420 q = 1) (hb : d184130 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183420, d184130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183420, d184130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183421 q = 1) (hb : d184131 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183421, d184131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183421, d184131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101711 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10391 q = 1) (hb : d101711 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23359 q ha hb
    | true =>
      simp only [d10391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10392 q = 1) (hb : d101711 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183422 q = 1) (hb : d184132 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183422, d184132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d183422, d184132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d183423 q = 1) (hb : d184133 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183423, d184133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183423, d184133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183424 q = 1) (hb : d184134 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183424, d184134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183424, d184134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101691 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10371 q = 1) (hb : d101691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10372 q = 1) (hb : d101691 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183407 q = 1) (hb : d184117 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183407, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d183407, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h16 (q : Pattern) (ha : d183408 q = 1) (hb : d184118 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183408, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183408, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h17 (q : Pattern) (ha : d183414 q = 1) (hb : d184124 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183414, d184124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d183414, d184124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h18 (q : Pattern) (ha : d183425 q = 1) (hb : d184135 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183425, d184135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183425, d184135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro41346 (p : Pattern) (ha : d183435 p = 1) (hb : d184145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5247 q = 1) (hb : d69330 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
    | true =>
      simp only [d5247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10401 q = 1) (hb : d69330 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183429 q = 1) (hb : d184139 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183429, d184139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183429, d184139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183430 q = 1) (hb : d184140 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183430, d184140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183430, d184140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d183431 q = 1) (hb : d184141 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183431, d184141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183431, d184141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101732 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10412 q = 1) (hb : d101732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10413 q = 1) (hb : d101732 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183432 q = 1) (hb : d184142 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183432, d184142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d183432, d184142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183433 q = 1) (hb : d184143 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183433, d184143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183433, d184143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d183434 q = 1) (hb : d184144 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183434, d184144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183434, d184144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d183435 q = 1) (hb : d184145 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183435, d184145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183435, d184145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41347 (p : Pattern) (ha : d183441 p = 1) (hb : d184151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183411 q = 1) (hb : d184121 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183411, d184121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41342 q ha hb
    | true =>
      simp only [d183411, d184121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41343 q ha hb
  have h2 (q : Pattern) (ha : d183412 q = 1) (hb : d184122 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183412, d184122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183412, d184122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183413 q = 1) (hb : d184123 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183413, d184123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183413, d184123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183416 q = 1) (hb : d184126 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183416, d184126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41343 q ha hb
    | true =>
      simp only [d183416, d184126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41344 q ha hb
  have h5 (q : Pattern) (ha : d183417 q = 1) (hb : d184127 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183417, d184127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183417, d184127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183418 q = 1) (hb : d184128 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183418, d184128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183418, d184128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183419 q = 1) (hb : d184129 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183419, d184129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183419, d184129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183426 q = 1) (hb : d184136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183426, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41343 q ha hb
    | true =>
      simp only [d183426, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41345 q ha hb
  have h9 (q : Pattern) (ha : d183427 q = 1) (hb : d184137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183427, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183427, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183428 q = 1) (hb : d184138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183428, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183428, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183436 q = 1) (hb : d184146 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183436, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41345 q ha hb
    | true =>
      simp only [d183436, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41346 q ha hb
  have h12 (q : Pattern) (ha : d183437 q = 1) (hb : d184147 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183437, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183437, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183438 q = 1) (hb : d184148 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183438, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183438, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d183439 q = 1) (hb : d184149 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183439, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183439, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183440 q = 1) (hb : d184150 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183440, d184150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183440, d184150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d183441 q = 1) (hb : d184151 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183441, d184151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183441, d184151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro41348 (p : Pattern) (ha : d183446 p = 1) (hb : d184156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183426 q = 1) (hb : d184136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183426, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41343 q ha hb
    | true =>
      simp only [d183426, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41345 q ha hb
  have h2 (q : Pattern) (ha : d183427 q = 1) (hb : d184137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183427, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183427, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183428 q = 1) (hb : d184138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183428, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183428, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183436 q = 1) (hb : d184146 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183436, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41345 q ha hb
    | true =>
      simp only [d183436, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41346 q ha hb
  have h5 (q : Pattern) (ha : d183437 q = 1) (hb : d184147 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183437, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183437, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183438 q = 1) (hb : d184148 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183438, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183438, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183439 q = 1) (hb : d184149 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183439, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183439, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183444 q = 1) (hb : d184154 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183444, d184154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183444, d184154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d183445 q = 1) (hb : d184155 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183445, d184155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183445, d184155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183446 q = 1) (hb : d184156 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183446, d184156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d183446, d184156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro41349 (p : Pattern) (ha : d183452 p = 1) (hb : d184162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183442 q = 1) (hb : d184152 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183442, d184152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41347 q ha hb
    | true =>
      simp only [d183442, d184152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183443 q = 1) (hb : d184153 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183443, d184153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183443, d184153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183447 q = 1) (hb : d184157 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183447, d184157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41348 q ha hb
    | true =>
      simp only [d183447, d184157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183448 q = 1) (hb : d184158 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183448, d184158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183448, d184158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183449 q = 1) (hb : d184159 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183449, d184159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183449, d184159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183450 q = 1) (hb : d184160 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183450, d184160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183450, d184160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183451 q = 1) (hb : d184161 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183451, d184161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183451, d184161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d183452 q = 1) (hb : d184162 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183452, d184162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183452, d184162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41350 (p : Pattern) (ha : d183456 p = 1) (hb : d184166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53343 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2065 q = 1) (hb : d53343 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10436 q = 1) (hb : d53343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183453 q = 1) (hb : d184163 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183453, d184163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183453, d184163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183454 q = 1) (hb : d184164 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183454, d184164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183454, d184164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d183455 q = 1) (hb : d184165 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183455, d184165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183455, d184165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101732 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10412 q = 1) (hb : d101732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10413 q = 1) (hb : d101732 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183432 q = 1) (hb : d184142 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183432, d184142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d183432, d184142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d183433 q = 1) (hb : d184143 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183433, d184143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183433, d184143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d183434 q = 1) (hb : d184144 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183434, d184144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d183434, d184144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d183456 q = 1) (hb : d184166 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183456, d184166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183456, d184166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41351 (p : Pattern) (ha : d183462 p = 1) (hb : d184172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183457 q = 1) (hb : d184167 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183457, d184167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41345 q ha hb
    | true =>
      simp only [d183457, d184167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41350 q ha hb
  have h2 (q : Pattern) (ha : d183458 q = 1) (hb : d184168 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183458, d184168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183458, d184168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183459 q = 1) (hb : d184169 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183459, d184169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183459, d184169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183460 q = 1) (hb : d184170 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183460, d184170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183460, d184170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183461 q = 1) (hb : d184171 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183461, d184171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183461, d184171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183462 q = 1) (hb : d184172 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183462, d184172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183462, d184172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41352 (p : Pattern) (ha : d183468 p = 1) (hb : d184178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183447 q = 1) (hb : d184157 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183447, d184157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41348 q ha hb
    | true =>
      simp only [d183447, d184157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183448 q = 1) (hb : d184158 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183448, d184158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183448, d184158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183463 q = 1) (hb : d184173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183463, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41351 q ha hb
    | true =>
      simp only [d183463, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183464 q = 1) (hb : d184174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183464, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183464, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183465 q = 1) (hb : d184175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183465, d184175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183465, d184175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183466 q = 1) (hb : d184176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183466, d184176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183466, d184176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183467 q = 1) (hb : d184177 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183467, d184177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183467, d184177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d183468 q = 1) (hb : d184178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183468, d184178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183468, d184178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41353 (p : Pattern) (ha : d183484 p = 1) (hb : d184181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53343 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2065 q = 1) (hb : d53343 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10436 q = 1) (hb : d53343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d183453 q = 1) (hb : d184163 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d183453, d184163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d183453, d184163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d183454 q = 1) (hb : d184164 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d183454, d184164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183454, d184164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d183455 q = 1) (hb : d184165 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d183455, d184165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183455, d184165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d183484 q = 1) (hb : d184181 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d183484, d184181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183484, d184181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h7 p ha hb
theorem andIntro41354 (p : Pattern) (ha : d183490 p = 1) (hb : d184187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183426 q = 1) (hb : d184136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183426, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41343 q ha hb
    | true =>
      simp only [d183426, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41345 q ha hb
  have h2 (q : Pattern) (ha : d183427 q = 1) (hb : d184137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183427, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183427, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183428 q = 1) (hb : d184138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183428, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183428, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183436 q = 1) (hb : d184146 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183436, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41345 q ha hb
    | true =>
      simp only [d183436, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41346 q ha hb
  have h5 (q : Pattern) (ha : d183437 q = 1) (hb : d184147 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183437, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183437, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183438 q = 1) (hb : d184148 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183438, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183438, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183439 q = 1) (hb : d184149 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183439, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183439, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183485 q = 1) (hb : d184182 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183485, d184182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41345 q ha hb
    | true =>
      simp only [d183485, d184182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41353 q ha hb
  have h9 (q : Pattern) (ha : d183486 q = 1) (hb : d184183 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183486, d184183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183486, d184183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183487 q = 1) (hb : d184184 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183487, d184184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183487, d184184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183488 q = 1) (hb : d184185 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183488, d184185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183488, d184185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d183489 q = 1) (hb : d184186 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183489, d184186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183489, d184186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183490 q = 1) (hb : d184187 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183490, d184187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d183490, d184187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41355 (p : Pattern) (ha : d183496 p = 1) (hb : d184193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183491 q = 1) (hb : d184188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183491, d184188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41354 q ha hb
    | true =>
      simp only [d183491, d184188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183492 q = 1) (hb : d184189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183492, d184189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183492, d184189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183493 q = 1) (hb : d184190 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183493, d184190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183493, d184190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183494 q = 1) (hb : d184191 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183494, d184191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183494, d184191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183495 q = 1) (hb : d184192 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183495, d184192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183495, d184192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183496 q = 1) (hb : d184193 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183496, d184193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183496, d184193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41356 (p : Pattern) (ha : d183502 p = 1) (hb : d184199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183469 q = 1) (hb : d184179 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183469, d184179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41349 q ha hb
    | true =>
      simp only [d183469, d184179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41352 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d183482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d183483 q = 1) (hb : d184180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183483, d184180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183483, d184180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d183497 q = 1) (hb : d184194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183497, d184194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41355 q ha hb
    | true =>
      simp only [d183497, d184194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183498 q = 1) (hb : d184195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183498, d184195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183498, d184195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183499 q = 1) (hb : d184196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183499, d184196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183499, d184196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183500 q = 1) (hb : d184197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183500, d184197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183500, d184197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183501 q = 1) (hb : d184198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183501, d184198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183501, d184198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183502 q = 1) (hb : d184199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183502, d184199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183502, d184199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41357 (p : Pattern) (ha : d183481 p = 1) (hb : d184204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183463 q = 1) (hb : d184173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183463, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41351 q ha hb
    | true =>
      simp only [d183463, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183464 q = 1) (hb : d184174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183464, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183464, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183478 q = 1) (hb : d184201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183478, d184201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183478, d184201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183479 q = 1) (hb : d184202 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183479, d184202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183479, d184202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183480 q = 1) (hb : d184203 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183480, d184203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183480, d184203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183481 q = 1) (hb : d184204 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183481, d184204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183481, d184204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41358 (p : Pattern) (ha : d183509 p = 1) (hb : d184210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183504 q = 1) (hb : d184205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183504, d184205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41357 q ha hb
    | true =>
      simp only [d183504, d184205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183505 q = 1) (hb : d184206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183505, d184206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183505, d184206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183506 q = 1) (hb : d184207 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183506, d184207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183506, d184207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183507 q = 1) (hb : d184208 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183507, d184208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183507, d184208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183508 q = 1) (hb : d184209 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183508, d184209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183508, d184209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183509 q = 1) (hb : d184210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183509, d184210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183509, d184210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41359 (p : Pattern) (ha : d183515 p = 1) (hb : d184216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183503 q = 1) (hb : d184200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183503, d184200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183503, d184200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41356 q ha hb
  have h2 (q : Pattern) (ha : d183510 q = 1) (hb : d184211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183510, d184211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183510, d184211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41358 q ha hb
  have h3 (q : Pattern) (ha : d183511 q = 1) (hb : d184212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d183511, d184212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183511, d184212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183512 q = 1) (hb : d184213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d183512, d184213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183512, d184213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183513 q = 1) (hb : d184214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d183513, d184214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183513, d184214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183514 q = 1) (hb : d184215 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d183514, d184215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183514, d184215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183515 q = 1) (hb : d184216 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d183515, d184216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183515, d184216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41360 (p : Pattern) (ha : d183521 p = 1) (hb : d184222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183516 q = 1) (hb : d184217 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d183516, d184217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183516, d184217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41359 q ha hb
  have h2 (q : Pattern) (ha : d183517 q = 1) (hb : d184218 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d183517, d184218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183517, d184218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183518 q = 1) (hb : d184219 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d183518, d184219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183518, d184219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183519 q = 1) (hb : d184220 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d183519, d184220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183519, d184220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183520 q = 1) (hb : d184221 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d183520, d184221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183520, d184221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183521 q = 1) (hb : d184222 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d183521, d184222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183521, d184222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41361 (p : Pattern) (ha : d183527 p = 1) (hb : d184228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d183028 q = 1) (hb : d183757 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d183028, d183757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41274 q ha hb
    | true =>
      simp only [d183028, d183757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41287 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d183118 q = 1) (hb : d183846 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d183118, d183846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183118, d183846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41303 q ha hb
  have h3 (q : Pattern) (ha : d183119 q = 1) (hb : d183847 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d183119, d183847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d183119, d183847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183252 q = 1) (hb : d183971 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d183252, d183971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183252, d183971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41322 q ha hb
  have h5 (q : Pattern) (ha : d183253 q = 1) (hb : d183972 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d183253, d183972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183253, d183972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183254 q = 1) (hb : d183973 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d183254, d183973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183254, d183973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183389 q = 1) (hb : d184099 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d183389, d184099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183389, d184099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41341 q ha hb
  have h8 (q : Pattern) (ha : d183390 q = 1) (hb : d184100 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d183390, d184100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183390, d184100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183391 q = 1) (hb : d184101 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d183391, d184101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183391, d184101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183392 q = 1) (hb : d184102 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d183392, d184102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183392, d184102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183522 q = 1) (hb : d184223 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d183522, d184223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183522, d184223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41360 q ha hb
  have h12 (q : Pattern) (ha : d183523 q = 1) (hb : d184224 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d183523, d184224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183523, d184224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183524 q = 1) (hb : d184225 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d183524, d184225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183524, d184225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d183525 q = 1) (hb : d184226 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d183525, d184226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183525, d184226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183526 q = 1) (hb : d184227 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d183526, d184227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183526, d184227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d183527 q = 1) (hb : d184228 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d183527, d184228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183527, d184228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro41362 (p : Pattern) (ha : d183533 p = 1) (hb : d184234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183528 q = 1) (hb : d184229 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d183528, d184229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41361 q ha hb
    | true =>
      simp only [d183528, d184229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183529 q = 1) (hb : d184230 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d183529, d184230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183529, d184230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183530 q = 1) (hb : d184231 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d183530, d184231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183530, d184231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183531 q = 1) (hb : d184232 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d183531, d184232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183531, d184232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183532 q = 1) (hb : d184233 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d183532, d184233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183532, d184233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183533 q = 1) (hb : d184234 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d183533, d184234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183533, d184234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41363 (p : Pattern) (ha : d183539 p = 1) (hb : d184240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183534 q = 1) (hb : d184235 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d183534, d184235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41362 q ha hb
    | true =>
      simp only [d183534, d184235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183535 q = 1) (hb : d184236 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d183535, d184236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183535, d184236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183536 q = 1) (hb : d184237 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d183536, d184237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183536, d184237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183537 q = 1) (hb : d184238 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d183537, d184238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183537, d184238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183538 q = 1) (hb : d184239 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d183538, d184239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183538, d184239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183539 q = 1) (hb : d184240 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d183539, d184240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183539, d184240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41364 (p : Pattern) (ha : d183545 p = 1) (hb : d184246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183540 q = 1) (hb : d184241 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d183540, d184241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41363 q ha hb
    | true =>
      simp only [d183540, d184241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183541 q = 1) (hb : d184242 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d183541, d184242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183541, d184242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183542 q = 1) (hb : d184243 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d183542, d184243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183542, d184243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183543 q = 1) (hb : d184244 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d183543, d184244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183543, d184244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183544 q = 1) (hb : d184245 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d183544, d184245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183544, d184245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183545 q = 1) (hb : d184246 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d183545, d184246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183545, d184246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41365 (p : Pattern) (ha : d183551 p = 1) (hb : d184252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183546 q = 1) (hb : d184247 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d183546, d184247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41364 q ha hb
    | true =>
      simp only [d183546, d184247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183547 q = 1) (hb : d184248 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d183547, d184248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183547, d184248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183548 q = 1) (hb : d184249 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d183548, d184249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183548, d184249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183549 q = 1) (hb : d184250 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d183549, d184250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183549, d184250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183550 q = 1) (hb : d184251 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d183550, d184251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183550, d184251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183551 q = 1) (hb : d184252 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d183551, d184252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183551, d184252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41366 (p : Pattern) (ha : d183557 p = 1) (hb : d184258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183552 q = 1) (hb : d184253 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d183552, d184253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41365 q ha hb
    | true =>
      simp only [d183552, d184253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183553 q = 1) (hb : d184254 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d183553, d184254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183553, d184254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183554 q = 1) (hb : d184255 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d183554, d184255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183554, d184255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183555 q = 1) (hb : d184256 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d183555, d184256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183555, d184256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183556 q = 1) (hb : d184257 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d183556, d184257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183556, d184257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183557 q = 1) (hb : d184258 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d183557, d184258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183557, d184258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41367 (p : Pattern) (ha : d183563 p = 1) (hb : d184264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183558 q = 1) (hb : d184259 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d183558, d184259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41366 q ha hb
    | true =>
      simp only [d183558, d184259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183559 q = 1) (hb : d184260 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d183559, d184260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183559, d184260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183560 q = 1) (hb : d184261 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d183560, d184261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183560, d184261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183561 q = 1) (hb : d184262 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d183561, d184262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183561, d184262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183562 q = 1) (hb : d184263 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d183562, d184263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183562, d184263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183563 q = 1) (hb : d184264 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d183563, d184264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183563, d184264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41368 (p : Pattern) (ha : d183569 p = 1) (hb : d184270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183564 q = 1) (hb : d184265 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d183564, d184265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41367 q ha hb
    | true =>
      simp only [d183564, d184265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183565 q = 1) (hb : d184266 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d183565, d184266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183565, d184266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183566 q = 1) (hb : d184267 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d183566, d184267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183566, d184267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183567 q = 1) (hb : d184268 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d183567, d184268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183567, d184268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183568 q = 1) (hb : d184269 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d183568, d184269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183568, d184269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183569 q = 1) (hb : d184270 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d183569, d184270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183569, d184270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41369 (p : Pattern) (ha : d61083 p = 1) (hb : d181811 p = 1) : d184275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17697 q = 1) (hb : d181811 q = 1) : d183672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, d183672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17697, d183672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41155 q ha hb
  have h2 (q : Pattern) (ha : d61079 q = 1) (hb : d181811 q = 1) : d184271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61079, d184271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61079, d184271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61080 q = 1) (hb : d181811 q = 1) : d184272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61080, d184272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61080, d184272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61081 q = 1) (hb : d181811 q = 1) : d184273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61081, d184273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61081, d184273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61082 q = 1) (hb : d181811 q = 1) : d184274 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61082, d184274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61082, d184274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61083 q = 1) (hb : d181811 q = 1) : d184275 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61083, d184275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61083, d184275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41370 (p : Pattern) (ha : d61093 p = 1) (hb : d181811 p = 1) : d184285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17609 q = 1) (hb : d181811 q = 1) : d183618 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, d183618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41152 q ha hb
    | true =>
      simp only [d17609, d183618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41147 q ha hb
  have h2 (q : Pattern) (ha : d61089 q = 1) (hb : d181811 q = 1) : d184281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d61089, d184281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61089, d184281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61090 q = 1) (hb : d181811 q = 1) : d184282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d61090, d184282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61090, d184282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61091 q = 1) (hb : d181811 q = 1) : d184283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d61091, d184283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61091, d184283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61092 q = 1) (hb : d181811 q = 1) : d184284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d61092, d184284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61092, d184284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61093 q = 1) (hb : d181811 q = 1) : d184285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d61093, d184285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61093, d184285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41371 (p : Pattern) (ha : d61099 p = 1) (hb : d181811 p = 1) : d184291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61094 q = 1) (hb : d181811 q = 1) : d184286 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61094, d184286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61094, d184286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41370 q ha hb
  have h2 (q : Pattern) (ha : d61095 q = 1) (hb : d181811 q = 1) : d184287 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61095, d184287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61095, d184287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61096 q = 1) (hb : d181811 q = 1) : d184288 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61096, d184288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61096, d184288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61097 q = 1) (hb : d181811 q = 1) : d184289 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61097, d184289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61097, d184289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61098 q = 1) (hb : d181811 q = 1) : d184290 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61098, d184290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61098, d184290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61099 q = 1) (hb : d181811 q = 1) : d184291 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61099, d184291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61099, d184291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41372 (p : Pattern) (ha : d61105 p = 1) (hb : d181811 p = 1) : d184297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61084 q = 1) (hb : d181811 q = 1) : d184276 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61084, d184276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61084, d184276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41369 q ha hb
  have h2 (q : Pattern) (ha : d61085 q = 1) (hb : d181811 q = 1) : d184277 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61085, d184277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61085, d184277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61086 q = 1) (hb : d181811 q = 1) : d184278 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61086, d184278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61086, d184278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61087 q = 1) (hb : d181811 q = 1) : d184279 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61087, d184279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61087, d184279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61088 q = 1) (hb : d181811 q = 1) : d184280 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61088, d184280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61088, d184280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61100 q = 1) (hb : d181811 q = 1) : d184292 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61100, d184292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61100, d184292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41371 q ha hb
  have h7 (q : Pattern) (ha : d61101 q = 1) (hb : d181811 q = 1) : d184293 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61101, d184293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61101, d184293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61102 q = 1) (hb : d181811 q = 1) : d184294 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61102, d184294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61102, d184294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61103 q = 1) (hb : d181811 q = 1) : d184295 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61103, d184295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61103, d184295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61104 q = 1) (hb : d181811 q = 1) : d184296 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61104, d184296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61104, d184296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61105 q = 1) (hb : d181811 q = 1) : d184297 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61105, d184297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61105, d184297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro41373 (p : Pattern) (ha : d173535 p = 1) (hb : d181811 p = 1) : d184303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173530 q = 1) (hb : d181811 q = 1) : d184298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173530, d184298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41171 q ha hb
    | true =>
      simp only [d173530, d184298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41164 q ha hb
  have h2 (q : Pattern) (ha : d173531 q = 1) (hb : d181811 q = 1) : d184299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173531, d184299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173531, d184299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173532 q = 1) (hb : d181811 q = 1) : d184300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173532, d184300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173532, d184300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173533 q = 1) (hb : d181811 q = 1) : d184301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173533, d184301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173533, d184301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173534 q = 1) (hb : d181811 q = 1) : d184302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173534, d184302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173534, d184302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173535 q = 1) (hb : d181811 q = 1) : d184303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173535, d184303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173535, d184303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41374 (p : Pattern) (ha : d173541 p = 1) (hb : d181811 p = 1) : d184309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173536 q = 1) (hb : d181811 q = 1) : d184304 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173536, d184304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173536, d184304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41373 q ha hb
  have h2 (q : Pattern) (ha : d173537 q = 1) (hb : d181811 q = 1) : d184305 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173537, d184305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173537, d184305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173538 q = 1) (hb : d181811 q = 1) : d184306 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173538, d184306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173538, d184306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173539 q = 1) (hb : d181811 q = 1) : d184307 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173539, d184307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173539, d184307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173540 q = 1) (hb : d181811 q = 1) : d184308 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173540, d184308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173540, d184308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173541 q = 1) (hb : d181811 q = 1) : d184309 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173541, d184309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173541, d184309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41375 (p : Pattern) (ha : d173547 p = 1) (hb : d181811 p = 1) : d184315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173542 q = 1) (hb : d181811 q = 1) : d184310 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173542, d184310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173542, d184310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41374 q ha hb
  have h2 (q : Pattern) (ha : d173543 q = 1) (hb : d181811 q = 1) : d184311 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173543, d184311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173543, d184311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173544 q = 1) (hb : d181811 q = 1) : d184312 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173544, d184312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173544, d184312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173545 q = 1) (hb : d181811 q = 1) : d184313 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173545, d184313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173545, d184313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173546 q = 1) (hb : d181811 q = 1) : d184314 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173546, d184314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173546, d184314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173547 q = 1) (hb : d181811 q = 1) : d184315 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173547, d184315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173547, d184315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41376 (p : Pattern) (ha : d173554 p = 1) (hb : d181811 p = 1) : d184322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173549 q = 1) (hb : d181811 q = 1) : d184317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173549, d184317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41187 q ha hb
    | true =>
      simp only [d173549, d184317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41179 q ha hb
  have h2 (q : Pattern) (ha : d173550 q = 1) (hb : d181811 q = 1) : d184318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173550, d184318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173550, d184318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173551 q = 1) (hb : d181811 q = 1) : d184319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173551, d184319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173551, d184319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173552 q = 1) (hb : d181811 q = 1) : d184320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173552, d184320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173552, d184320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173553 q = 1) (hb : d181811 q = 1) : d184321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173553, d184321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173553, d184321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173554 q = 1) (hb : d181811 q = 1) : d184322 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173554, d184322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173554, d184322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41377 (p : Pattern) (ha : d173560 p = 1) (hb : d181811 p = 1) : d184328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173555 q = 1) (hb : d181811 q = 1) : d184323 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173555, d184323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173555, d184323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41376 q ha hb
  have h2 (q : Pattern) (ha : d173556 q = 1) (hb : d181811 q = 1) : d184324 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173556, d184324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173556, d184324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173557 q = 1) (hb : d181811 q = 1) : d184325 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173557, d184325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173557, d184325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173558 q = 1) (hb : d181811 q = 1) : d184326 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173558, d184326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173558, d184326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173559 q = 1) (hb : d181811 q = 1) : d184327 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173559, d184327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173559, d184327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173560 q = 1) (hb : d181811 q = 1) : d184328 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173560, d184328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173560, d184328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41378 (p : Pattern) (ha : d173566 p = 1) (hb : d181811 p = 1) : d184334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173561 q = 1) (hb : d181811 q = 1) : d184329 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173561, d184329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173561, d184329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41377 q ha hb
  have h2 (q : Pattern) (ha : d173562 q = 1) (hb : d181811 q = 1) : d184330 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173562, d184330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173562, d184330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173563 q = 1) (hb : d181811 q = 1) : d184331 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173563, d184331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173563, d184331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173564 q = 1) (hb : d181811 q = 1) : d184332 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173564, d184332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173564, d184332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173565 q = 1) (hb : d181811 q = 1) : d184333 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173565, d184333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173565, d184333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173566 q = 1) (hb : d181811 q = 1) : d184334 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173566, d184334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173566, d184334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41379 (p : Pattern) (ha : d173570 p = 1) (hb : d181811 p = 1) : d184338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d181811 q = 1) : d183886 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41198 q ha hb
    | true =>
      simp only [d17980, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41192 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d181811 q = 1) : d183887 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d181811 q = 1) : d183888 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d181811 q = 1) : d183896 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41192 q ha hb
    | true =>
      simp only [d17990, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41200 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d181811 q = 1) : d183897 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d181811 q = 1) : d183898 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d181811 q = 1) : d183899 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18009 q = 1) (hb : d181811 q = 1) : d183915 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18009, d183915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41192 q ha hb
    | true =>
      simp only [d18009, d183915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41193 q ha hb
  have h9 (q : Pattern) (ha : d18010 q = 1) (hb : d181811 q = 1) : d183916 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18010, d183916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18010, d183916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18011 q = 1) (hb : d181811 q = 1) : d183917 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, d183917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18011, d183917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18012 q = 1) (hb : d181811 q = 1) : d183918 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, d183918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18012, d183918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d173569 q = 1) (hb : d181811 q = 1) : d184337 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173569, d184337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173569, d184337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d173570 q = 1) (hb : d181811 q = 1) : d184338 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173570, d184338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d173570, d184338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41380 (p : Pattern) (ha : d173576 p = 1) (hb : d181811 p = 1) : d184344 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173571 q = 1) (hb : d181811 q = 1) : d184339 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173571, d184339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41379 q ha hb
    | true =>
      simp only [d173571, d184339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173572 q = 1) (hb : d181811 q = 1) : d184340 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173572, d184340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173572, d184340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18015 q = 1) (hb : d181811 q = 1) : d183921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41194 q ha hb
    | true =>
      simp only [d18015, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18016 q = 1) (hb : d181811 q = 1) : d183922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173573 q = 1) (hb : d181811 q = 1) : d184341 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173573, d184341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173573, d184341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173574 q = 1) (hb : d181811 q = 1) : d184342 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173574, d184342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173574, d184342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d173575 q = 1) (hb : d181811 q = 1) : d184343 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173575, d184343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173575, d184343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d173576 q = 1) (hb : d181811 q = 1) : d184344 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173576, d184344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173576, d184344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41381 (p : Pattern) (ha : d173582 p = 1) (hb : d181811 p = 1) : d184350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173577 q = 1) (hb : d181811 q = 1) : d184345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173577, d184345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41380 q ha hb
    | true =>
      simp only [d173577, d184345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41195 q ha hb
  have h2 (q : Pattern) (ha : d173578 q = 1) (hb : d181811 q = 1) : d184346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173578, d184346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173578, d184346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173579 q = 1) (hb : d181811 q = 1) : d184347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173579, d184347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173579, d184347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173580 q = 1) (hb : d181811 q = 1) : d184348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173580, d184348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173580, d184348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173581 q = 1) (hb : d181811 q = 1) : d184349 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173581, d184349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173581, d184349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173582 q = 1) (hb : d181811 q = 1) : d184350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173582, d184350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173582, d184350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41382 (p : Pattern) (ha : d173588 p = 1) (hb : d181811 p = 1) : d184356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173583 q = 1) (hb : d181811 q = 1) : d184351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173583, d184351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173583, d184351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41381 q ha hb
  have h2 (q : Pattern) (ha : d173584 q = 1) (hb : d181811 q = 1) : d184352 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173584, d184352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173584, d184352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173585 q = 1) (hb : d181811 q = 1) : d184353 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173585, d184353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173585, d184353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173586 q = 1) (hb : d181811 q = 1) : d184354 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173586, d184354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173586, d184354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173587 q = 1) (hb : d181811 q = 1) : d184355 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173587, d184355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173587, d184355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173588 q = 1) (hb : d181811 q = 1) : d184356 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173588, d184356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173588, d184356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41383 (p : Pattern) (ha : d173594 p = 1) (hb : d181811 p = 1) : d184362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173589 q = 1) (hb : d181811 q = 1) : d184357 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173589, d184357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173589, d184357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41382 q ha hb
  have h2 (q : Pattern) (ha : d173590 q = 1) (hb : d181811 q = 1) : d184358 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173590, d184358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173590, d184358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173591 q = 1) (hb : d181811 q = 1) : d184359 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173591, d184359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173591, d184359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173592 q = 1) (hb : d181811 q = 1) : d184360 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173592, d184360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173592, d184360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173593 q = 1) (hb : d181811 q = 1) : d184361 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173593, d184361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173593, d184361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173594 q = 1) (hb : d181811 q = 1) : d184362 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173594, d184362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173594, d184362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41384 (p : Pattern) (ha : d173599 p = 1) (hb : d181811 p = 1) : d184367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d181811 q = 1) : d184012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41217 q ha hb
    | true =>
      simp only [d18161, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41211 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d181811 q = 1) : d184013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d181811 q = 1) : d184014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d181811 q = 1) : d184022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41211 q ha hb
    | true =>
      simp only [d18171, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41219 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d181811 q = 1) : d184023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d181811 q = 1) : d184024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d181811 q = 1) : d184025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18192 q = 1) (hb : d181811 q = 1) : d184043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18192, d184043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41211 q ha hb
    | true =>
      simp only [d18192, d184043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41212 q ha hb
  have h9 (q : Pattern) (ha : d18193 q = 1) (hb : d181811 q = 1) : d184044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18193, d184044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18193, d184044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18194 q = 1) (hb : d181811 q = 1) : d184045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, d184045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18194, d184045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18195 q = 1) (hb : d181811 q = 1) : d184046 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, d184046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18195, d184046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d173598 q = 1) (hb : d181811 q = 1) : d184366 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173598, d184366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173598, d184366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d173599 q = 1) (hb : d181811 q = 1) : d184367 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173599, d184367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d173599, d184367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41385 (p : Pattern) (ha : d173605 p = 1) (hb : d181811 p = 1) : d184373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173600 q = 1) (hb : d181811 q = 1) : d184368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173600, d184368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41384 q ha hb
    | true =>
      simp only [d173600, d184368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173601 q = 1) (hb : d181811 q = 1) : d184369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173601, d184369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173601, d184369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18198 q = 1) (hb : d181811 q = 1) : d184049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41213 q ha hb
    | true =>
      simp only [d18198, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18199 q = 1) (hb : d181811 q = 1) : d184050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173602 q = 1) (hb : d181811 q = 1) : d184370 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173602, d184370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173602, d184370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173603 q = 1) (hb : d181811 q = 1) : d184371 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173603, d184371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173603, d184371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d173604 q = 1) (hb : d181811 q = 1) : d184372 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173604, d184372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173604, d184372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d173605 q = 1) (hb : d181811 q = 1) : d184373 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173605, d184373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173605, d184373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41386 (p : Pattern) (ha : d173611 p = 1) (hb : d181811 p = 1) : d184379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173606 q = 1) (hb : d181811 q = 1) : d184374 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173606, d184374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41385 q ha hb
    | true =>
      simp only [d173606, d184374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41214 q ha hb
  have h2 (q : Pattern) (ha : d173607 q = 1) (hb : d181811 q = 1) : d184375 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173607, d184375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173607, d184375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173608 q = 1) (hb : d181811 q = 1) : d184376 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173608, d184376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173608, d184376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173609 q = 1) (hb : d181811 q = 1) : d184377 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173609, d184377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173609, d184377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173610 q = 1) (hb : d181811 q = 1) : d184378 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173610, d184378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173610, d184378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173611 q = 1) (hb : d181811 q = 1) : d184379 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173611, d184379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173611, d184379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41387 (p : Pattern) (ha : d173617 p = 1) (hb : d181811 p = 1) : d184385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173612 q = 1) (hb : d181811 q = 1) : d184380 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173612, d184380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173612, d184380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41386 q ha hb
  have h2 (q : Pattern) (ha : d173613 q = 1) (hb : d181811 q = 1) : d184381 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173613, d184381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173613, d184381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173614 q = 1) (hb : d181811 q = 1) : d184382 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173614, d184382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173614, d184382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173615 q = 1) (hb : d181811 q = 1) : d184383 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173615, d184383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173615, d184383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173616 q = 1) (hb : d181811 q = 1) : d184384 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173616, d184384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173616, d184384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173617 q = 1) (hb : d181811 q = 1) : d184385 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173617, d184385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173617, d184385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41388 (p : Pattern) (ha : d173623 p = 1) (hb : d181811 p = 1) : d184391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173618 q = 1) (hb : d181811 q = 1) : d184386 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173618, d184386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173618, d184386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41387 q ha hb
  have h2 (q : Pattern) (ha : d173619 q = 1) (hb : d181811 q = 1) : d184387 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173619, d184387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173619, d184387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173620 q = 1) (hb : d181811 q = 1) : d184388 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173620, d184388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173620, d184388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173621 q = 1) (hb : d181811 q = 1) : d184389 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173621, d184389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173621, d184389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173622 q = 1) (hb : d181811 q = 1) : d184390 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173622, d184390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173622, d184390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173623 q = 1) (hb : d181811 q = 1) : d184391 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173623, d184391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173623, d184391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41389 (p : Pattern) (ha : d173629 p = 1) (hb : d181811 p = 1) : d184397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d181811 q = 1) : d184136 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41236 q ha hb
    | true =>
      simp only [d18342, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41230 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d181811 q = 1) : d184137 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d181811 q = 1) : d184138 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d181811 q = 1) : d184146 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41230 q ha hb
    | true =>
      simp only [d18352, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41238 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d181811 q = 1) : d184147 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d181811 q = 1) : d184148 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d181811 q = 1) : d184149 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18373 q = 1) (hb : d181811 q = 1) : d184167 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18373, d184167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41230 q ha hb
    | true =>
      simp only [d18373, d184167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41231 q ha hb
  have h9 (q : Pattern) (ha : d18374 q = 1) (hb : d181811 q = 1) : d184168 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18374, d184168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18374, d184168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18375 q = 1) (hb : d181811 q = 1) : d184169 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, d184169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18375, d184169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18376 q = 1) (hb : d181811 q = 1) : d184170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, d184170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18376, d184170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d173628 q = 1) (hb : d181811 q = 1) : d184396 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173628, d184396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173628, d184396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d173629 q = 1) (hb : d181811 q = 1) : d184397 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173629, d184397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d173629, d184397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41390 (p : Pattern) (ha : d173635 p = 1) (hb : d181811 p = 1) : d184403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173630 q = 1) (hb : d181811 q = 1) : d184398 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173630, d184398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41389 q ha hb
    | true =>
      simp only [d173630, d184398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173631 q = 1) (hb : d181811 q = 1) : d184399 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173631, d184399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173631, d184399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d181811 q = 1) : d184173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41232 q ha hb
    | true =>
      simp only [d18379, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d181811 q = 1) : d184174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173632 q = 1) (hb : d181811 q = 1) : d184400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173632, d184400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173632, d184400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173633 q = 1) (hb : d181811 q = 1) : d184401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173633, d184401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173633, d184401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d173634 q = 1) (hb : d181811 q = 1) : d184402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173634, d184402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173634, d184402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d173635 q = 1) (hb : d181811 q = 1) : d184403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173635, d184403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173635, d184403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41391 (p : Pattern) (ha : d173641 p = 1) (hb : d181811 p = 1) : d184409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173636 q = 1) (hb : d181811 q = 1) : d184404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173636, d184404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41390 q ha hb
    | true =>
      simp only [d173636, d184404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41233 q ha hb
  have h2 (q : Pattern) (ha : d173637 q = 1) (hb : d181811 q = 1) : d184405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173637, d184405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173637, d184405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173638 q = 1) (hb : d181811 q = 1) : d184406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173638, d184406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173638, d184406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173639 q = 1) (hb : d181811 q = 1) : d184407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173639, d184407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173639, d184407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173640 q = 1) (hb : d181811 q = 1) : d184408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173640, d184408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173640, d184408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173641 q = 1) (hb : d181811 q = 1) : d184409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173641, d184409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173641, d184409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41392 (p : Pattern) (ha : d173647 p = 1) (hb : d181811 p = 1) : d184415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173642 q = 1) (hb : d181811 q = 1) : d184410 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173642, d184410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173642, d184410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41391 q ha hb
  have h2 (q : Pattern) (ha : d173643 q = 1) (hb : d181811 q = 1) : d184411 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173643, d184411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173643, d184411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173644 q = 1) (hb : d181811 q = 1) : d184412 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173644, d184412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173644, d184412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173645 q = 1) (hb : d181811 q = 1) : d184413 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173645, d184413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173645, d184413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173646 q = 1) (hb : d181811 q = 1) : d184414 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173646, d184414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173646, d184414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173647 q = 1) (hb : d181811 q = 1) : d184415 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173647, d184415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173647, d184415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41393 (p : Pattern) (ha : d173653 p = 1) (hb : d181811 p = 1) : d184421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173648 q = 1) (hb : d181811 q = 1) : d184416 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173648, d184416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173648, d184416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41392 q ha hb
  have h2 (q : Pattern) (ha : d173649 q = 1) (hb : d181811 q = 1) : d184417 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173649, d184417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173649, d184417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173650 q = 1) (hb : d181811 q = 1) : d184418 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173650, d184418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173650, d184418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173651 q = 1) (hb : d181811 q = 1) : d184419 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173651, d184419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173651, d184419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173652 q = 1) (hb : d181811 q = 1) : d184420 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173652, d184420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173652, d184420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173653 q = 1) (hb : d181811 q = 1) : d184421 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173653, d184421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173653, d184421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41394 (p : Pattern) (ha : d173659 p = 1) (hb : d181811 p = 1) : d184427 p = 1 := by
  have h0 (q : Pattern) (ha : d173548 q = 1) (hb : d181811 q = 1) : d184316 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173548, d184316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41372 q ha hb
    | true =>
      simp only [d173548, d184316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41375 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d173567 q = 1) (hb : d181811 q = 1) : d184335 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173567, d184335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173567, d184335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41378 q ha hb
  have h3 (q : Pattern) (ha : d173568 q = 1) (hb : d181811 q = 1) : d184336 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173568, d184336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173568, d184336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173595 q = 1) (hb : d181811 q = 1) : d184363 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173595, d184363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173595, d184363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41383 q ha hb
  have h5 (q : Pattern) (ha : d173596 q = 1) (hb : d181811 q = 1) : d184364 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173596, d184364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173596, d184364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173597 q = 1) (hb : d181811 q = 1) : d184365 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173597, d184365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173597, d184365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d173624 q = 1) (hb : d181811 q = 1) : d184392 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173624, d184392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173624, d184392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41388 q ha hb
  have h8 (q : Pattern) (ha : d173625 q = 1) (hb : d181811 q = 1) : d184393 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173625, d184393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173625, d184393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d173626 q = 1) (hb : d181811 q = 1) : d184394 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173626, d184394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173626, d184394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d173627 q = 1) (hb : d181811 q = 1) : d184395 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d173627, d184395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173627, d184395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d173654 q = 1) (hb : d181811 q = 1) : d184422 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173654, d184422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173654, d184422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41393 q ha hb
  have h12 (q : Pattern) (ha : d173655 q = 1) (hb : d181811 q = 1) : d184423 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173655, d184423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173655, d184423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d173656 q = 1) (hb : d181811 q = 1) : d184424 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173656, d184424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173656, d184424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d173657 q = 1) (hb : d181811 q = 1) : d184425 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d173657, d184425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173657, d184425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d173658 q = 1) (hb : d181811 q = 1) : d184426 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d173658, d184426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d173658, d184426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d173659 q = 1) (hb : d181811 q = 1) : d184427 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d173659, d184427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d173659, d184427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro41395 (p : Pattern) (ha : d173665 p = 1) (hb : d181811 p = 1) : d184433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173660 q = 1) (hb : d181811 q = 1) : d184428 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d173660, d184428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41394 q ha hb
    | true =>
      simp only [d173660, d184428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173661 q = 1) (hb : d181811 q = 1) : d184429 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d173661, d184429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173661, d184429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173662 q = 1) (hb : d181811 q = 1) : d184430 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d173662, d184430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173662, d184430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173663 q = 1) (hb : d181811 q = 1) : d184431 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d173663, d184431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173663, d184431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173664 q = 1) (hb : d181811 q = 1) : d184432 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d173664, d184432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173664, d184432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173665 q = 1) (hb : d181811 q = 1) : d184433 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d173665, d184433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173665, d184433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41396 (p : Pattern) (ha : d173671 p = 1) (hb : d181811 p = 1) : d184439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173666 q = 1) (hb : d181811 q = 1) : d184434 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d173666, d184434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41395 q ha hb
    | true =>
      simp only [d173666, d184434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173667 q = 1) (hb : d181811 q = 1) : d184435 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d173667, d184435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173667, d184435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173668 q = 1) (hb : d181811 q = 1) : d184436 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d173668, d184436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173668, d184436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173669 q = 1) (hb : d181811 q = 1) : d184437 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d173669, d184437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173669, d184437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173670 q = 1) (hb : d181811 q = 1) : d184438 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d173670, d184438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173670, d184438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173671 q = 1) (hb : d181811 q = 1) : d184439 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d173671, d184439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173671, d184439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41397 (p : Pattern) (ha : d173677 p = 1) (hb : d181811 p = 1) : d184445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173672 q = 1) (hb : d181811 q = 1) : d184440 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d173672, d184440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41396 q ha hb
    | true =>
      simp only [d173672, d184440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173673 q = 1) (hb : d181811 q = 1) : d184441 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d173673, d184441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173673, d184441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173674 q = 1) (hb : d181811 q = 1) : d184442 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d173674, d184442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173674, d184442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173675 q = 1) (hb : d181811 q = 1) : d184443 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d173675, d184443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173675, d184443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173676 q = 1) (hb : d181811 q = 1) : d184444 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d173676, d184444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173676, d184444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173677 q = 1) (hb : d181811 q = 1) : d184445 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d173677, d184445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173677, d184445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41398 (p : Pattern) (ha : d173683 p = 1) (hb : d181811 p = 1) : d184451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173678 q = 1) (hb : d181811 q = 1) : d184446 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d173678, d184446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41397 q ha hb
    | true =>
      simp only [d173678, d184446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173679 q = 1) (hb : d181811 q = 1) : d184447 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d173679, d184447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173679, d184447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173680 q = 1) (hb : d181811 q = 1) : d184448 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d173680, d184448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173680, d184448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173681 q = 1) (hb : d181811 q = 1) : d184449 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d173681, d184449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173681, d184449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173682 q = 1) (hb : d181811 q = 1) : d184450 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d173682, d184450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173682, d184450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173683 q = 1) (hb : d181811 q = 1) : d184451 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d173683, d184451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173683, d184451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41399 (p : Pattern) (ha : d173689 p = 1) (hb : d181811 p = 1) : d184457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173684 q = 1) (hb : d181811 q = 1) : d184452 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d173684, d184452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41398 q ha hb
    | true =>
      simp only [d173684, d184452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173685 q = 1) (hb : d181811 q = 1) : d184453 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d173685, d184453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173685, d184453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173686 q = 1) (hb : d181811 q = 1) : d184454 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d173686, d184454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173686, d184454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173687 q = 1) (hb : d181811 q = 1) : d184455 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d173687, d184455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173687, d184455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173688 q = 1) (hb : d181811 q = 1) : d184456 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d173688, d184456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173688, d184456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173689 q = 1) (hb : d181811 q = 1) : d184457 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d173689, d184457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173689, d184457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41400 (p : Pattern) (ha : d173695 p = 1) (hb : d181811 p = 1) : d184463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173690 q = 1) (hb : d181811 q = 1) : d184458 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d173690, d184458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41399 q ha hb
    | true =>
      simp only [d173690, d184458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173691 q = 1) (hb : d181811 q = 1) : d184459 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d173691, d184459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173691, d184459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173692 q = 1) (hb : d181811 q = 1) : d184460 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d173692, d184460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173692, d184460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173693 q = 1) (hb : d181811 q = 1) : d184461 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d173693, d184461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173693, d184461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173694 q = 1) (hb : d181811 q = 1) : d184462 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d173694, d184462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173694, d184462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173695 q = 1) (hb : d181811 q = 1) : d184463 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d173695, d184463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173695, d184463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41401 (p : Pattern) (ha : d173701 p = 1) (hb : d181811 p = 1) : d184469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173696 q = 1) (hb : d181811 q = 1) : d184464 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d173696, d184464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41400 q ha hb
    | true =>
      simp only [d173696, d184464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173697 q = 1) (hb : d181811 q = 1) : d184465 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d173697, d184465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173697, d184465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173698 q = 1) (hb : d181811 q = 1) : d184466 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d173698, d184466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173698, d184466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173699 q = 1) (hb : d181811 q = 1) : d184467 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d173699, d184467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173699, d184467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173700 q = 1) (hb : d181811 q = 1) : d184468 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d173700, d184468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173700, d184468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173701 q = 1) (hb : d181811 q = 1) : d184469 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d173701, d184469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173701, d184469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41402 (p : Pattern) (ha : d182893 p = 1) (hb : d183671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d182888 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d182856 q = 1) (hb : d183586 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182856, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41259 q ha hb
    | true =>
      simp only [d182856, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d182889 q = 1) (hb : d183667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182889, d183667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182889, d183667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d182857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d182890 q = 1) (hb : d183668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182890, d183668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182890, d183668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d182891 q = 1) (hb : d183669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182891, d183669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182891, d183669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d182892 q = 1) (hb : d183670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182892, d183670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182892, d183670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d182893 q = 1) (hb : d183671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182893, d183671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182893, d183671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41403 (p : Pattern) (ha : d182899 p = 1) (hb : d184275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182894 q = 1) (hb : d183672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182894, d183672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182894, d183672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41402 q ha hb
  have h2 (q : Pattern) (ha : d182895 q = 1) (hb : d184271 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182895, d184271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d182895, d184271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d182896 q = 1) (hb : d184272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182896, d184272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d182896, d184272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d182897 q = 1) (hb : d184273 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182897, d184273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182897, d184273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182898 q = 1) (hb : d184274 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182898, d184274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182898, d184274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182899 q = 1) (hb : d184275 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182899, d184275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182899, d184275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41404 (p : Pattern) (ha : d182935 p = 1) (hb : d184285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d182924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d182888 q = 1) (hb : d183618 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182888, d183618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41264 q ha hb
    | true =>
      simp only [d182888, d183618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41259 q ha hb
  have h3 (q : Pattern) (ha : d182925 q = 1) (hb : d184281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182925, d184281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182925, d184281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d182931 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d182932 q = 1) (hb : d184282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182932, d184282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182932, d184282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d182933 q = 1) (hb : d184283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182933, d184283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182933, d184283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d182934 q = 1) (hb : d184284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182934, d184284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182934, d184284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d182935 q = 1) (hb : d184285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182935, d184285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182935, d184285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41405 (p : Pattern) (ha : d182947 p = 1) (hb : d184291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d182936 q = 1) (hb : d184286 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182936, d184286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182936, d184286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41404 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d182942 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d182943 q = 1) (hb : d184287 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182943, d184287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d182943, d184287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d182944 q = 1) (hb : d184288 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182944, d184288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d182944, d184288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d182945 q = 1) (hb : d184289 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182945, d184289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d182945, d184289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d182946 q = 1) (hb : d184290 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182946, d184290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d182946, d184290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d182947 q = 1) (hb : d184291 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182947, d184291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182947, d184291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41406 (p : Pattern) (ha : d182953 p = 1) (hb : d184297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d182871 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d182900 q = 1) (hb : d184276 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182900, d184276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182900, d184276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41403 q ha hb
  have h3 (q : Pattern) (ha : d182901 q = 1) (hb : d184277 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182901, d184277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182901, d184277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d182902 q = 1) (hb : d184278 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182902, d184278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182902, d184278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d182903 q = 1) (hb : d184279 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182903, d184279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182903, d184279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d182904 q = 1) (hb : d184280 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182904, d184280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d182904, d184280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d182948 q = 1) (hb : d184292 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182948, d184292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182948, d184292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41405 q ha hb
  have h8 (q : Pattern) (ha : d182949 q = 1) (hb : d184293 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182949, d184293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182949, d184293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d182950 q = 1) (hb : d184294 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182950, d184294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182950, d184294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d182951 q = 1) (hb : d184295 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182951, d184295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182951, d184295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d182952 q = 1) (hb : d184296 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182952, d184296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182952, d184296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d182953 q = 1) (hb : d184297 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182953, d184297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d182953, d184297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro41407 (p : Pattern) (ha : d183008 p = 1) (hb : d184303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d182992 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d182997 q = 1) (hb : d184298 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182997, d184298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41281 q ha hb
    | true =>
      simp only [d182997, d184298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41284 q ha hb
  have h3 (q : Pattern) (ha : d182998 q = 1) (hb : d184299 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182998, d184299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d182998, d184299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d183004 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d183005 q = 1) (hb : d184300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183005, d184300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183005, d184300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d183006 q = 1) (hb : d184301 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183006, d184301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183006, d184301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183007 q = 1) (hb : d184302 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183007, d184302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183007, d184302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183008 q = 1) (hb : d184303 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183008, d184303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183008, d184303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41408 (p : Pattern) (ha : d183021 p = 1) (hb : d184309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183009 q = 1) (hb : d184304 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183009, d184304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183009, d184304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41407 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d183016 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d183017 q = 1) (hb : d184305 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d183017, d184305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183017, d184305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d183018 q = 1) (hb : d184306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d183018, d184306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183018, d184306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183019 q = 1) (hb : d184307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d183019, d184307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183019, d184307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183020 q = 1) (hb : d184308 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d183020, d184308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183020, d184308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183021 q = 1) (hb : d184309 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d183021, d184309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183021, d184309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41409 (p : Pattern) (ha : d183027 p = 1) (hb : d184315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183022 q = 1) (hb : d184310 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d183022, d184310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183022, d184310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41408 q ha hb
  have h2 (q : Pattern) (ha : d183023 q = 1) (hb : d184311 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d183023, d184311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183023, d184311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183024 q = 1) (hb : d184312 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d183024, d184312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183024, d184312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183025 q = 1) (hb : d184313 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d183025, d184313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183025, d184313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183026 q = 1) (hb : d184314 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d183026, d184314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183026, d184314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183027 q = 1) (hb : d184315 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d183027, d184315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183027, d184315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41410 (p : Pattern) (ha : d183098 p = 1) (hb : d184322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d183082 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d183087 q = 1) (hb : d184317 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183087, d184317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41297 q ha hb
    | true =>
      simp only [d183087, d184317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41300 q ha hb
  have h3 (q : Pattern) (ha : d183088 q = 1) (hb : d184318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183088, d184318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183088, d184318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d183094 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d183095 q = 1) (hb : d184319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183095, d184319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183095, d184319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d183096 q = 1) (hb : d184320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183096, d184320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183096, d184320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183097 q = 1) (hb : d184321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183097, d184321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183097, d184321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183098 q = 1) (hb : d184322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183098, d184322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183098, d184322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41411 (p : Pattern) (ha : d183111 p = 1) (hb : d184328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183099 q = 1) (hb : d184323 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183099, d184323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183099, d184323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41410 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d183106 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d183107 q = 1) (hb : d184324 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d183107, d184324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183107, d184324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d183108 q = 1) (hb : d184325 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d183108, d184325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183108, d184325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183109 q = 1) (hb : d184326 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d183109, d184326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183109, d184326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183110 q = 1) (hb : d184327 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d183110, d184327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183110, d184327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183111 q = 1) (hb : d184328 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d183111, d184328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183111, d184328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41412 (p : Pattern) (ha : d183117 p = 1) (hb : d184334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183112 q = 1) (hb : d184329 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d183112, d184329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183112, d184329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41411 q ha hb
  have h2 (q : Pattern) (ha : d183113 q = 1) (hb : d184330 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d183113, d184330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183113, d184330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183114 q = 1) (hb : d184331 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d183114, d184331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183114, d184331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183115 q = 1) (hb : d184332 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d183115, d184332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183115, d184332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183116 q = 1) (hb : d184333 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d183116, d184333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183116, d184333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183117 q = 1) (hb : d184334 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d183117, d184334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183117, d184334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41413 (p : Pattern) (ha : d183201 p = 1) (hb : d184338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183158 q = 1) (hb : d183886 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183158, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41305 q ha hb
    | true =>
      simp only [d183158, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41307 q ha hb
  have h2 (q : Pattern) (ha : d183159 q = 1) (hb : d183887 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183159, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183159, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183160 q = 1) (hb : d183888 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183160, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183160, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183168 q = 1) (hb : d183896 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183168, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41307 q ha hb
    | true =>
      simp only [d183168, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41308 q ha hb
  have h5 (q : Pattern) (ha : d183169 q = 1) (hb : d183897 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183169, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183169, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183170 q = 1) (hb : d183898 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183170, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183170, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183171 q = 1) (hb : d183899 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183171, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183171, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183187 q = 1) (hb : d183915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183187, d183915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41307 q ha hb
    | true =>
      simp only [d183187, d183915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41312 q ha hb
  have h9 (q : Pattern) (ha : d183188 q = 1) (hb : d183916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183188, d183916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183188, d183916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183189 q = 1) (hb : d183917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183189, d183917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183189, d183917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183190 q = 1) (hb : d183918 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183190, d183918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183190, d183918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d183200 q = 1) (hb : d184337 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183200, d184337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183200, d184337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183201 q = 1) (hb : d184338 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183201, d184338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d183201, d184338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41414 (p : Pattern) (ha : d183207 p = 1) (hb : d184344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183202 q = 1) (hb : d184339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183202, d184339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41413 q ha hb
    | true =>
      simp only [d183202, d184339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183203 q = 1) (hb : d184340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183203, d184340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183203, d184340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183193 q = 1) (hb : d183921 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183193, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41313 q ha hb
    | true =>
      simp only [d183193, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183194 q = 1) (hb : d183922 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183194, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183194, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183204 q = 1) (hb : d184341 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183204, d184341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183204, d184341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183205 q = 1) (hb : d184342 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183205, d184342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183205, d184342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183206 q = 1) (hb : d184343 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183206, d184343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183206, d184343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d183207 q = 1) (hb : d184344 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183207, d184344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183207, d184344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41415 (p : Pattern) (ha : d183232 p = 1) (hb : d184350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d183199 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d183212 q = 1) (hb : d184345 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183212, d184345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41414 q ha hb
    | true =>
      simp only [d183212, d184345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41319 q ha hb
  have h3 (q : Pattern) (ha : d183213 q = 1) (hb : d184346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183213, d184346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183213, d184346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d183228 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d183229 q = 1) (hb : d184347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183229, d184347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183229, d184347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d183230 q = 1) (hb : d184348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183230, d184348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183230, d184348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183231 q = 1) (hb : d184349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183231, d184349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183231, d184349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183232 q = 1) (hb : d184350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183232, d184350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183232, d184350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41416 (p : Pattern) (ha : d183245 p = 1) (hb : d184356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183233 q = 1) (hb : d184351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183233, d184351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183233, d184351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41415 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d183240 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d183241 q = 1) (hb : d184352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d183241, d184352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183241, d184352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d183242 q = 1) (hb : d184353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d183242, d184353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183242, d184353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183243 q = 1) (hb : d184354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d183243, d184354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183243, d184354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183244 q = 1) (hb : d184355 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d183244, d184355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183244, d184355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183245 q = 1) (hb : d184356 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d183245, d184356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183245, d184356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41417 (p : Pattern) (ha : d183251 p = 1) (hb : d184362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183246 q = 1) (hb : d184357 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d183246, d184357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183246, d184357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41416 q ha hb
  have h2 (q : Pattern) (ha : d183247 q = 1) (hb : d184358 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d183247, d184358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183247, d184358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183248 q = 1) (hb : d184359 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d183248, d184359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183248, d184359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183249 q = 1) (hb : d184360 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d183249, d184360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183249, d184360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183250 q = 1) (hb : d184361 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d183250, d184361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183250, d184361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183251 q = 1) (hb : d184362 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d183251, d184362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183251, d184362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41418 (p : Pattern) (ha : d183338 p = 1) (hb : d184367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183293 q = 1) (hb : d184012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183293, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41324 q ha hb
    | true =>
      simp only [d183293, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41326 q ha hb
  have h2 (q : Pattern) (ha : d183294 q = 1) (hb : d184013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183294, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183294, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183295 q = 1) (hb : d184014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183295, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183295, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183303 q = 1) (hb : d184022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183303, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41326 q ha hb
    | true =>
      simp only [d183303, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41327 q ha hb
  have h5 (q : Pattern) (ha : d183304 q = 1) (hb : d184023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183304, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183304, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183305 q = 1) (hb : d184024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183305, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183305, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183306 q = 1) (hb : d184025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183306, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183306, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183324 q = 1) (hb : d184043 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183324, d184043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41326 q ha hb
    | true =>
      simp only [d183324, d184043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41331 q ha hb
  have h9 (q : Pattern) (ha : d183325 q = 1) (hb : d184044 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183325, d184044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183325, d184044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183326 q = 1) (hb : d184045 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183326, d184045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183326, d184045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183327 q = 1) (hb : d184046 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183327, d184046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183327, d184046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d183337 q = 1) (hb : d184366 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183337, d184366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183337, d184366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183338 q = 1) (hb : d184367 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183338, d184367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d183338, d184367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41419 (p : Pattern) (ha : d183344 p = 1) (hb : d184373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183339 q = 1) (hb : d184368 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183339, d184368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41418 q ha hb
    | true =>
      simp only [d183339, d184368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183340 q = 1) (hb : d184369 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183340, d184369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183340, d184369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183330 q = 1) (hb : d184049 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183330, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41332 q ha hb
    | true =>
      simp only [d183330, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183331 q = 1) (hb : d184050 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183331, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183331, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183341 q = 1) (hb : d184370 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183341, d184370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183341, d184370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183342 q = 1) (hb : d184371 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183342, d184371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183342, d184371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183343 q = 1) (hb : d184372 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183343, d184372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183343, d184372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d183344 q = 1) (hb : d184373 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183344, d184373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183344, d184373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41420 (p : Pattern) (ha : d183369 p = 1) (hb : d184379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d183336 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d183349 q = 1) (hb : d184374 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183349, d184374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41419 q ha hb
    | true =>
      simp only [d183349, d184374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41338 q ha hb
  have h3 (q : Pattern) (ha : d183350 q = 1) (hb : d184375 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183350, d184375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183350, d184375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d183365 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d183366 q = 1) (hb : d184376 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183366, d184376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183366, d184376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d183367 q = 1) (hb : d184377 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183367, d184377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183367, d184377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183368 q = 1) (hb : d184378 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183368, d184378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183368, d184378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183369 q = 1) (hb : d184379 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183369, d184379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183369, d184379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41421 (p : Pattern) (ha : d183382 p = 1) (hb : d184385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183370 q = 1) (hb : d184380 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183370, d184380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183370, d184380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41420 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d183377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d183378 q = 1) (hb : d184381 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d183378, d184381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183378, d184381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d183379 q = 1) (hb : d184382 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d183379, d184382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183379, d184382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183380 q = 1) (hb : d184383 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d183380, d184383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183380, d184383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183381 q = 1) (hb : d184384 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d183381, d184384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183381, d184384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183382 q = 1) (hb : d184385 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d183382, d184385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183382, d184385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41422 (p : Pattern) (ha : d183388 p = 1) (hb : d184391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183383 q = 1) (hb : d184386 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d183383, d184386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183383, d184386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41421 q ha hb
  have h2 (q : Pattern) (ha : d183384 q = 1) (hb : d184387 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d183384, d184387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183384, d184387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183385 q = 1) (hb : d184388 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d183385, d184388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183385, d184388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183386 q = 1) (hb : d184389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d183386, d184389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183386, d184389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183387 q = 1) (hb : d184390 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d183387, d184390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183387, d184390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183388 q = 1) (hb : d184391 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d183388, d184391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183388, d184391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41423 (p : Pattern) (ha : d183471 p = 1) (hb : d184397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183426 q = 1) (hb : d184136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183426, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41343 q ha hb
    | true =>
      simp only [d183426, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41345 q ha hb
  have h2 (q : Pattern) (ha : d183427 q = 1) (hb : d184137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183427, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183427, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183428 q = 1) (hb : d184138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183428, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183428, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183436 q = 1) (hb : d184146 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183436, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41345 q ha hb
    | true =>
      simp only [d183436, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41346 q ha hb
  have h5 (q : Pattern) (ha : d183437 q = 1) (hb : d184147 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183437, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183437, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183438 q = 1) (hb : d184148 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183438, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183438, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183439 q = 1) (hb : d184149 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183439, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183439, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183457 q = 1) (hb : d184167 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d183457, d184167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41345 q ha hb
    | true =>
      simp only [d183457, d184167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41350 q ha hb
  have h9 (q : Pattern) (ha : d183458 q = 1) (hb : d184168 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d183458, d184168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183458, d184168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183459 q = 1) (hb : d184169 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d183459, d184169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183459, d184169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183460 q = 1) (hb : d184170 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d183460, d184170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183460, d184170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d183470 q = 1) (hb : d184396 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d183470, d184396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183470, d184396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183471 q = 1) (hb : d184397 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d183471, d184397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d183471, d184397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41424 (p : Pattern) (ha : d183477 p = 1) (hb : d184403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183472 q = 1) (hb : d184398 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183472, d184398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41423 q ha hb
    | true =>
      simp only [d183472, d184398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183473 q = 1) (hb : d184399 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183473, d184399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183473, d184399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183463 q = 1) (hb : d184173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d183463, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41351 q ha hb
    | true =>
      simp only [d183463, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183464 q = 1) (hb : d184174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183464, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183464, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183474 q = 1) (hb : d184400 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d183474, d184400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183474, d184400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183475 q = 1) (hb : d184401 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d183475, d184401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183475, d184401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183476 q = 1) (hb : d184402 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d183476, d184402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183476, d184402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d183477 q = 1) (hb : d184403 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d183477, d184403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d183477, d184403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41425 (p : Pattern) (ha : d183502 p = 1) (hb : d184409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d183469 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d183482 q = 1) (hb : d184404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d183482, d184404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41424 q ha hb
    | true =>
      simp only [d183482, d184404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41357 q ha hb
  have h3 (q : Pattern) (ha : d183483 q = 1) (hb : d184405 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183483, d184405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183483, d184405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d183498 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d183499 q = 1) (hb : d184406 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183499, d184406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183499, d184406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d183500 q = 1) (hb : d184407 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183500, d184407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183500, d184407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183501 q = 1) (hb : d184408 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183501, d184408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183501, d184408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183502 q = 1) (hb : d184409 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183502, d184409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183502, d184409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41426 (p : Pattern) (ha : d183515 p = 1) (hb : d184415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183503 q = 1) (hb : d184410 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183503, d184410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183503, d184410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41425 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d183510 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d183511 q = 1) (hb : d184411 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d183511, d184411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183511, d184411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d183512 q = 1) (hb : d184412 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d183512, d184412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183512, d184412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183513 q = 1) (hb : d184413 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d183513, d184413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183513, d184413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183514 q = 1) (hb : d184414 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d183514, d184414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183514, d184414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d183515 q = 1) (hb : d184415 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d183515, d184415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183515, d184415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41427 (p : Pattern) (ha : d183521 p = 1) (hb : d184421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183516 q = 1) (hb : d184416 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d183516, d184416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183516, d184416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41426 q ha hb
  have h2 (q : Pattern) (ha : d183517 q = 1) (hb : d184417 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d183517, d184417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183517, d184417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d183518 q = 1) (hb : d184418 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d183518, d184418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183518, d184418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183519 q = 1) (hb : d184419 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d183519, d184419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183519, d184419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d183520 q = 1) (hb : d184420 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d183520, d184420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183520, d184420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183521 q = 1) (hb : d184421 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d183521, d184421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d183521, d184421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41428 (p : Pattern) (ha : d183527 p = 1) (hb : d184427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d183028 q = 1) (hb : d184316 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d183028, d184316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41406 q ha hb
    | true =>
      simp only [d183028, d184316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41409 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d183118 q = 1) (hb : d184335 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d183118, d184335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183118, d184335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41412 q ha hb
  have h3 (q : Pattern) (ha : d183119 q = 1) (hb : d184336 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d183119, d184336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d183119, d184336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d183252 q = 1) (hb : d184363 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d183252, d184363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183252, d184363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41417 q ha hb
  have h5 (q : Pattern) (ha : d183253 q = 1) (hb : d184364 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d183253, d184364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183253, d184364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183254 q = 1) (hb : d184365 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d183254, d184365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183254, d184365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183389 q = 1) (hb : d184392 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d183389, d184392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183389, d184392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41422 q ha hb
  have h8 (q : Pattern) (ha : d183390 q = 1) (hb : d184393 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d183390, d184393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183390, d184393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d183391 q = 1) (hb : d184394 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d183391, d184394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183391, d184394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d183392 q = 1) (hb : d184395 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d183392, d184395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d183392, d184395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d183522 q = 1) (hb : d184422 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d183522, d184422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183522, d184422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41427 q ha hb
  have h12 (q : Pattern) (ha : d183523 q = 1) (hb : d184423 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d183523, d184423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183523, d184423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d183524 q = 1) (hb : d184424 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d183524, d184424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183524, d184424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d183525 q = 1) (hb : d184425 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d183525, d184425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d183525, d184425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d183526 q = 1) (hb : d184426 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d183526, d184426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d183526, d184426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d183527 q = 1) (hb : d184427 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d183527, d184427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d183527, d184427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro41429 (p : Pattern) (ha : d183533 p = 1) (hb : d184433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183528 q = 1) (hb : d184428 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d183528, d184428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41428 q ha hb
    | true =>
      simp only [d183528, d184428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183529 q = 1) (hb : d184429 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d183529, d184429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183529, d184429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183530 q = 1) (hb : d184430 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d183530, d184430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183530, d184430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183531 q = 1) (hb : d184431 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d183531, d184431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183531, d184431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183532 q = 1) (hb : d184432 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d183532, d184432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183532, d184432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183533 q = 1) (hb : d184433 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d183533, d184433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183533, d184433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41430 (p : Pattern) (ha : d183539 p = 1) (hb : d184439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183534 q = 1) (hb : d184434 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d183534, d184434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41429 q ha hb
    | true =>
      simp only [d183534, d184434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183535 q = 1) (hb : d184435 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d183535, d184435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183535, d184435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183536 q = 1) (hb : d184436 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d183536, d184436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183536, d184436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183537 q = 1) (hb : d184437 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d183537, d184437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183537, d184437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183538 q = 1) (hb : d184438 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d183538, d184438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183538, d184438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183539 q = 1) (hb : d184439 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d183539, d184439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183539, d184439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41431 (p : Pattern) (ha : d183545 p = 1) (hb : d184445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183540 q = 1) (hb : d184440 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d183540, d184440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41430 q ha hb
    | true =>
      simp only [d183540, d184440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183541 q = 1) (hb : d184441 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d183541, d184441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183541, d184441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183542 q = 1) (hb : d184442 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d183542, d184442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183542, d184442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183543 q = 1) (hb : d184443 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d183543, d184443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183543, d184443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183544 q = 1) (hb : d184444 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d183544, d184444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183544, d184444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183545 q = 1) (hb : d184445 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d183545, d184445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183545, d184445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41432 (p : Pattern) (ha : d183551 p = 1) (hb : d184451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183546 q = 1) (hb : d184446 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d183546, d184446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41431 q ha hb
    | true =>
      simp only [d183546, d184446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183547 q = 1) (hb : d184447 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d183547, d184447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183547, d184447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183548 q = 1) (hb : d184448 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d183548, d184448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183548, d184448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183549 q = 1) (hb : d184449 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d183549, d184449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183549, d184449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183550 q = 1) (hb : d184450 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d183550, d184450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183550, d184450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183551 q = 1) (hb : d184451 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d183551, d184451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183551, d184451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41433 (p : Pattern) (ha : d183557 p = 1) (hb : d184457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183552 q = 1) (hb : d184452 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d183552, d184452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41432 q ha hb
    | true =>
      simp only [d183552, d184452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183553 q = 1) (hb : d184453 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d183553, d184453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183553, d184453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183554 q = 1) (hb : d184454 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d183554, d184454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183554, d184454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183555 q = 1) (hb : d184455 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d183555, d184455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183555, d184455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183556 q = 1) (hb : d184456 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d183556, d184456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183556, d184456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183557 q = 1) (hb : d184457 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d183557, d184457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183557, d184457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41434 (p : Pattern) (ha : d183563 p = 1) (hb : d184463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183558 q = 1) (hb : d184458 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d183558, d184458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41433 q ha hb
    | true =>
      simp only [d183558, d184458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183559 q = 1) (hb : d184459 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d183559, d184459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183559, d184459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183560 q = 1) (hb : d184460 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d183560, d184460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183560, d184460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183561 q = 1) (hb : d184461 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d183561, d184461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183561, d184461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183562 q = 1) (hb : d184462 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d183562, d184462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183562, d184462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183563 q = 1) (hb : d184463 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d183563, d184463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183563, d184463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41435 (p : Pattern) (ha : d183569 p = 1) (hb : d184469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183564 q = 1) (hb : d184464 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d183564, d184464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41434 q ha hb
    | true =>
      simp only [d183564, d184464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d183565 q = 1) (hb : d184465 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d183565, d184465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183565, d184465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d183566 q = 1) (hb : d184466 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d183566, d184466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d183566, d184466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d183567 q = 1) (hb : d184467 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d183567, d184467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183567, d184467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d183568 q = 1) (hb : d184468 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d183568, d184468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d183568, d184468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d183569 q = 1) (hb : d184469 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d183569, d184469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d183569, d184469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41436 (p : Pattern) (ha : d183671 p = 1) (hb : d184474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d181915 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d183586 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d183667 q = 1) (hb : d184470 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d183667, d184470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d183667, d184470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d181884 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d183668 q = 1) (hb : d184471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d183668, d184471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d183668, d184471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d183669 q = 1) (hb : d184472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d183669, d184472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d183669, d184472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d183670 q = 1) (hb : d184473 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d183670, d184473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d183670, d184473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d183671 q = 1) (hb : d184474 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d183671, d184474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d183671, d184474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41437 (p : Pattern) (ha : d184275 p = 1) (hb : d184480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d183672 q = 1) (hb : d184475 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d183672, d184475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d183672, d184475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41436 q ha hb
  have h2 (q : Pattern) (ha : d184271 q = 1) (hb : d184476 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184271, d184476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184271, d184476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d184272 q = 1) (hb : d184477 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184272, d184477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d184272, d184477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d184273 q = 1) (hb : d184478 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184273, d184478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184273, d184478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184274 q = 1) (hb : d184479 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184274, d184479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184274, d184479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184275 q = 1) (hb : d184480 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d184275, d184480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184275, d184480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41438 (p : Pattern) (ha : d184285 p = 1) (hb : d184490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d181968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d183618 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184281 q = 1) (hb : d184486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184281, d184486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184281, d184486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d181992 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d184282 q = 1) (hb : d184487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184282, d184487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184282, d184487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184283 q = 1) (hb : d184488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184283, d184488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184283, d184488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d184284 q = 1) (hb : d184489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184284, d184489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184284, d184489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d184285 q = 1) (hb : d184490 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184285, d184490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184285, d184490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41439 (p : Pattern) (ha : d184291 p = 1) (hb : d184496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184286 q = 1) (hb : d184491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184286, d184491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184286, d184491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41438 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d182003 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184287 q = 1) (hb : d184492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184287, d184492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184287, d184492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184288 q = 1) (hb : d184493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184288, d184493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184288, d184493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184289 q = 1) (hb : d184494 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184289, d184494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184289, d184494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184290 q = 1) (hb : d184495 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184290, d184495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184290, d184495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d184291 q = 1) (hb : d184496 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d184291, d184496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184291, d184496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41440 (p : Pattern) (ha : d184297 p = 1) (hb : d184502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181898 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d184276 q = 1) (hb : d184481 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d184276, d184481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184276, d184481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41437 q ha hb
  have h3 (q : Pattern) (ha : d184277 q = 1) (hb : d184482 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d184277, d184482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184277, d184482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184278 q = 1) (hb : d184483 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d184278, d184483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184278, d184483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d184279 q = 1) (hb : d184484 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d184279, d184484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184279, d184484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184280 q = 1) (hb : d184485 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d184280, d184485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184280, d184485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d184292 q = 1) (hb : d184497 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d184292, d184497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184292, d184497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41439 q ha hb
  have h8 (q : Pattern) (ha : d184293 q = 1) (hb : d184498 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d184293, d184498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184293, d184498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d184294 q = 1) (hb : d184499 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d184294, d184499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184294, d184499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d184295 q = 1) (hb : d184500 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d184295, d184500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184295, d184500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d184296 q = 1) (hb : d184501 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d184296, d184501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184296, d184501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d184297 q = 1) (hb : d184502 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d184297, d184502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d184297, d184502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro41441 (p : Pattern) (ha : d184303 p = 1) (hb : d184507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d182053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d184298 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184299 q = 1) (hb : d184503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184299, d184503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184299, d184503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d182089 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d184300 q = 1) (hb : d184504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184300, d184504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184300, d184504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184301 q = 1) (hb : d184505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184301, d184505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184301, d184505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d184302 q = 1) (hb : d184506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184302, d184506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184302, d184506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d184303 q = 1) (hb : d184507 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184303, d184507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184303, d184507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41442 (p : Pattern) (ha : d184309 p = 1) (hb : d184513 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184304 q = 1) (hb : d184508 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184304, d184508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184304, d184508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41441 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d182105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184305 q = 1) (hb : d184509 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184305, d184509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184305, d184509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184306 q = 1) (hb : d184510 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184306, d184510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184306, d184510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184307 q = 1) (hb : d184511 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184307, d184511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184307, d184511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184308 q = 1) (hb : d184512 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184308, d184512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184308, d184512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d184309 q = 1) (hb : d184513 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d184309, d184513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184309, d184513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41443 (p : Pattern) (ha : d184315 p = 1) (hb : d184519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184310 q = 1) (hb : d184514 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d184310, d184514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184310, d184514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41442 q ha hb
  have h2 (q : Pattern) (ha : d184311 q = 1) (hb : d184515 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d184311, d184515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184311, d184515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d184312 q = 1) (hb : d184516 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d184312, d184516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184312, d184516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184313 q = 1) (hb : d184517 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d184313, d184517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184313, d184517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d184314 q = 1) (hb : d184518 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d184314, d184518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184314, d184518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184315 q = 1) (hb : d184519 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d184315, d184519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184315, d184519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41444 (p : Pattern) (ha : d184322 p = 1) (hb : d184525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d182171 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d184317 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184318 q = 1) (hb : d184521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184318, d184521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184318, d184521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d182218 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d184319 q = 1) (hb : d184522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184319, d184522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184319, d184522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184320 q = 1) (hb : d184523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184320, d184523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184320, d184523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d184321 q = 1) (hb : d184524 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184321, d184524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184321, d184524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d184322 q = 1) (hb : d184525 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184322, d184525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184322, d184525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41445 (p : Pattern) (ha : d184328 p = 1) (hb : d184531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184323 q = 1) (hb : d184526 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184323, d184526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184323, d184526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41444 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d182234 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184324 q = 1) (hb : d184527 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184324, d184527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184324, d184527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184325 q = 1) (hb : d184528 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184325, d184528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184325, d184528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184326 q = 1) (hb : d184529 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184326, d184529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184326, d184529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184327 q = 1) (hb : d184530 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184327, d184530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184327, d184530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d184328 q = 1) (hb : d184531 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d184328, d184531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184328, d184531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41446 (p : Pattern) (ha : d184334 p = 1) (hb : d184537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184329 q = 1) (hb : d184532 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d184329, d184532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184329, d184532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41445 q ha hb
  have h2 (q : Pattern) (ha : d184330 q = 1) (hb : d184533 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d184330, d184533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184330, d184533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d184331 q = 1) (hb : d184534 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d184331, d184534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184331, d184534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184332 q = 1) (hb : d184535 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d184332, d184535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184332, d184535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d184333 q = 1) (hb : d184536 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d184333, d184536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184333, d184536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184334 q = 1) (hb : d184537 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d184334, d184537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184334, d184537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41447 (p : Pattern) (ha : d184350 p = 1) (hb : d184544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d182327 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d184345 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184346 q = 1) (hb : d184540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184346, d184540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184346, d184540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d182398 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d184347 q = 1) (hb : d184541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184347, d184541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184347, d184541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184348 q = 1) (hb : d184542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184348, d184542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184348, d184542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d184349 q = 1) (hb : d184543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184349, d184543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184349, d184543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d184350 q = 1) (hb : d184544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184350, d184544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184350, d184544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41448 (p : Pattern) (ha : d184356 p = 1) (hb : d184550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184351 q = 1) (hb : d184545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184351, d184545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184351, d184545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41447 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d182414 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184352 q = 1) (hb : d184546 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184352, d184546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184352, d184546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184353 q = 1) (hb : d184547 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184353, d184547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184353, d184547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184354 q = 1) (hb : d184548 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184354, d184548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184354, d184548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184355 q = 1) (hb : d184549 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184355, d184549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184355, d184549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d184356 q = 1) (hb : d184550 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d184356, d184550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184356, d184550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41449 (p : Pattern) (ha : d184362 p = 1) (hb : d184556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184357 q = 1) (hb : d184551 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d184357, d184551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184357, d184551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41448 q ha hb
  have h2 (q : Pattern) (ha : d184358 q = 1) (hb : d184552 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d184358, d184552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184358, d184552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d184359 q = 1) (hb : d184553 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d184359, d184553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184359, d184553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184360 q = 1) (hb : d184554 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d184360, d184554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184360, d184554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d184361 q = 1) (hb : d184555 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d184361, d184555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184361, d184555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184362 q = 1) (hb : d184556 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d184362, d184556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184362, d184556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41450 (p : Pattern) (ha : d184379 p = 1) (hb : d184564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d182510 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d184374 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184375 q = 1) (hb : d184560 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184375, d184560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184375, d184560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d182583 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d184376 q = 1) (hb : d184561 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184376, d184561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184376, d184561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184377 q = 1) (hb : d184562 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184377, d184562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184377, d184562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d184378 q = 1) (hb : d184563 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184378, d184563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184378, d184563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d184379 q = 1) (hb : d184564 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184379, d184564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184379, d184564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41451 (p : Pattern) (ha : d184385 p = 1) (hb : d184570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184380 q = 1) (hb : d184565 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184380, d184565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184380, d184565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41450 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d182599 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184381 q = 1) (hb : d184566 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184381, d184566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184381, d184566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184382 q = 1) (hb : d184567 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184382, d184567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184382, d184567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184383 q = 1) (hb : d184568 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184383, d184568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184383, d184568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184384 q = 1) (hb : d184569 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184384, d184569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184384, d184569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d184385 q = 1) (hb : d184570 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d184385, d184570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184385, d184570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41452 (p : Pattern) (ha : d184391 p = 1) (hb : d184576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184386 q = 1) (hb : d184571 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d184386, d184571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184386, d184571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41451 q ha hb
  have h2 (q : Pattern) (ha : d184387 q = 1) (hb : d184572 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d184387, d184572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184387, d184572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d184388 q = 1) (hb : d184573 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d184388, d184573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184388, d184573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184389 q = 1) (hb : d184574 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d184389, d184574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184389, d184574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d184390 q = 1) (hb : d184575 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d184390, d184575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184390, d184575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184391 q = 1) (hb : d184576 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d184391, d184576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184391, d184576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41453 (p : Pattern) (ha : d184409 p = 1) (hb : d184585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d182691 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d184404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184405 q = 1) (hb : d184581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184405, d184581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184405, d184581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d182764 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d184406 q = 1) (hb : d184582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184406, d184582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184406, d184582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184407 q = 1) (hb : d184583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184407, d184583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184407, d184583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d184408 q = 1) (hb : d184584 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184408, d184584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184408, d184584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d184409 q = 1) (hb : d184585 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184409, d184585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184409, d184585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41454 (p : Pattern) (ha : d184415 p = 1) (hb : d184591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184410 q = 1) (hb : d184586 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184410, d184586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184410, d184586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41453 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d182780 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d184411 q = 1) (hb : d184587 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184411, d184587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184411, d184587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184412 q = 1) (hb : d184588 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184412, d184588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184412, d184588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184413 q = 1) (hb : d184589 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184413, d184589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184413, d184589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184414 q = 1) (hb : d184590 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184414, d184590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184414, d184590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d184415 q = 1) (hb : d184591 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d184415, d184591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184415, d184591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41455 (p : Pattern) (ha : d184421 p = 1) (hb : d184597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184416 q = 1) (hb : d184592 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d184416, d184592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184416, d184592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41454 q ha hb
  have h2 (q : Pattern) (ha : d184417 q = 1) (hb : d184593 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d184417, d184593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184417, d184593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d184418 q = 1) (hb : d184594 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d184418, d184594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184418, d184594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184419 q = 1) (hb : d184595 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d184419, d184595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184419, d184595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d184420 q = 1) (hb : d184596 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d184420, d184596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184420, d184596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184421 q = 1) (hb : d184597 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d184421, d184597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184421, d184597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41456 (p : Pattern) (ha : d184427 p = 1) (hb : d184603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d184316 q = 1) (hb : d184520 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d184316, d184520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41440 q ha hb
    | true =>
      simp only [d184316, d184520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41443 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d184335 q = 1) (hb : d184538 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d184335, d184538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184335, d184538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41446 q ha hb
  have h3 (q : Pattern) (ha : d184336 q = 1) (hb : d184539 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d184336, d184539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d184336, d184539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d184363 q = 1) (hb : d184557 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d184363, d184557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184363, d184557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41449 q ha hb
  have h5 (q : Pattern) (ha : d184364 q = 1) (hb : d184558 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d184364, d184558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184364, d184558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d184365 q = 1) (hb : d184559 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d184365, d184559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184365, d184559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d184392 q = 1) (hb : d184577 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d184392, d184577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184392, d184577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41452 q ha hb
  have h8 (q : Pattern) (ha : d184393 q = 1) (hb : d184578 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d184393, d184578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184393, d184578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d184394 q = 1) (hb : d184579 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d184394, d184579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184394, d184579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d184395 q = 1) (hb : d184580 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d184395, d184580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d184395, d184580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d184422 q = 1) (hb : d184598 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d184422, d184598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184422, d184598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41455 q ha hb
  have h12 (q : Pattern) (ha : d184423 q = 1) (hb : d184599 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d184423, d184599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184423, d184599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d184424 q = 1) (hb : d184600 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d184424, d184600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184424, d184600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d184425 q = 1) (hb : d184601 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d184425, d184601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184425, d184601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d184426 q = 1) (hb : d184602 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d184426, d184602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d184426, d184602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d184427 q = 1) (hb : d184603 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d184427, d184603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d184427, d184603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro41457 (p : Pattern) (ha : d184433 p = 1) (hb : d184609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184428 q = 1) (hb : d184604 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d184428, d184604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41456 q ha hb
    | true =>
      simp only [d184428, d184604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d184429 q = 1) (hb : d184605 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d184429, d184605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184429, d184605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d184430 q = 1) (hb : d184606 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d184430, d184606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d184430, d184606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d184431 q = 1) (hb : d184607 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d184431, d184607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184431, d184607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184432 q = 1) (hb : d184608 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d184432, d184608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184432, d184608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184433 q = 1) (hb : d184609 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d184433, d184609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184433, d184609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41458 (p : Pattern) (ha : d184439 p = 1) (hb : d184615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184434 q = 1) (hb : d184610 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d184434, d184610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41457 q ha hb
    | true =>
      simp only [d184434, d184610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d184435 q = 1) (hb : d184611 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d184435, d184611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184435, d184611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d184436 q = 1) (hb : d184612 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d184436, d184612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d184436, d184612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d184437 q = 1) (hb : d184613 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d184437, d184613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184437, d184613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184438 q = 1) (hb : d184614 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d184438, d184614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184438, d184614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184439 q = 1) (hb : d184615 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d184439, d184615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184439, d184615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41459 (p : Pattern) (ha : d184445 p = 1) (hb : d184621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184440 q = 1) (hb : d184616 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d184440, d184616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41458 q ha hb
    | true =>
      simp only [d184440, d184616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d184441 q = 1) (hb : d184617 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d184441, d184617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184441, d184617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d184442 q = 1) (hb : d184618 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d184442, d184618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d184442, d184618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d184443 q = 1) (hb : d184619 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d184443, d184619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184443, d184619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184444 q = 1) (hb : d184620 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d184444, d184620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184444, d184620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184445 q = 1) (hb : d184621 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d184445, d184621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184445, d184621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41460 (p : Pattern) (ha : d184451 p = 1) (hb : d184627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184446 q = 1) (hb : d184622 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d184446, d184622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41459 q ha hb
    | true =>
      simp only [d184446, d184622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d184447 q = 1) (hb : d184623 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d184447, d184623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184447, d184623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d184448 q = 1) (hb : d184624 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d184448, d184624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d184448, d184624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d184449 q = 1) (hb : d184625 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d184449, d184625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184449, d184625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184450 q = 1) (hb : d184626 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d184450, d184626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184450, d184626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184451 q = 1) (hb : d184627 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d184451, d184627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184451, d184627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41461 (p : Pattern) (ha : d184457 p = 1) (hb : d184633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184452 q = 1) (hb : d184628 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d184452, d184628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41460 q ha hb
    | true =>
      simp only [d184452, d184628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d184453 q = 1) (hb : d184629 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d184453, d184629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184453, d184629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d184454 q = 1) (hb : d184630 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d184454, d184630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d184454, d184630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d184455 q = 1) (hb : d184631 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d184455, d184631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184455, d184631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184456 q = 1) (hb : d184632 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d184456, d184632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184456, d184632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184457 q = 1) (hb : d184633 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d184457, d184633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184457, d184633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41462 (p : Pattern) (ha : d184463 p = 1) (hb : d184639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184458 q = 1) (hb : d184634 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d184458, d184634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41461 q ha hb
    | true =>
      simp only [d184458, d184634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d184459 q = 1) (hb : d184635 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d184459, d184635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184459, d184635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d184460 q = 1) (hb : d184636 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d184460, d184636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d184460, d184636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d184461 q = 1) (hb : d184637 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d184461, d184637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184461, d184637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184462 q = 1) (hb : d184638 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d184462, d184638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184462, d184638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184463 q = 1) (hb : d184639 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d184463, d184639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184463, d184639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41463 (p : Pattern) (ha : d184469 p = 1) (hb : d184645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d184464 q = 1) (hb : d184640 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d184464, d184640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41462 q ha hb
    | true =>
      simp only [d184464, d184640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d184465 q = 1) (hb : d184641 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d184465, d184641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d184465, d184641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d184466 q = 1) (hb : d184642 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d184466, d184642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d184466, d184642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d184467 q = 1) (hb : d184643 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d184467, d184643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d184467, d184643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d184468 q = 1) (hb : d184644 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d184468, d184644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d184468, d184644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d184469 q = 1) (hb : d184645 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d184469, d184645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d184469, d184645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41464 (p : Pattern) (ha : d128579 p = 1) (hb : d129470 p = 1) : d129470 p = 1 := by
  have h0 (q : Pattern) (ha : d128579 q = 1) (hb : d129470 q = 1) : d129470 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro41465 (p : Pattern) (ha : d17564 p = 1) (hb : d51923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17561 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17561, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17562 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17562, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17563 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17563, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17564 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17564, d51923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17564, d51923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41466 (p : Pattern) (ha : d17570 p = 1) (hb : d51929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17565 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41465 q ha hb
    | true =>
      simp only [d17565, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17566 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17567 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17568 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17568, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17569 q = 1) (hb : d51928 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17569, d51928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17569, d51928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17570 q = 1) (hb : d51929 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17570, d51929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17570, d51929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41467 (p : Pattern) (ha : d17576 p = 1) (hb : d51935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17571 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41466 q ha hb
    | true =>
      simp only [d17571, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17572 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17572, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17573 q = 1) (hb : d51932 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17573, d51932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17573, d51932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17574 q = 1) (hb : d51933 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17574, d51933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17574, d51933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17575 q = 1) (hb : d51934 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17575, d51934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17575, d51934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17576 q = 1) (hb : d51935 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17576, d51935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17576, d51935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41468 (p : Pattern) (ha : d17582 p = 1) (hb : d51941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17577 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41467 q ha hb
    | true =>
      simp only [d17577, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17578 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17578, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17579 q = 1) (hb : d51938 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17579, d51938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17579, d51938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17580 q = 1) (hb : d51939 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17580, d51939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17580, d51939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17581 q = 1) (hb : d51940 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17581, d51940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17581, d51940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17582 q = 1) (hb : d51941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17582, d51941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17582, d51941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41469 (p : Pattern) (ha : d17588 p = 1) (hb : d51947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51917 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17583 q = 1) (hb : d51942 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17583, d51942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17583, d51942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41468 q ha hb
  have h3 (q : Pattern) (ha : d17584 q = 1) (hb : d51943 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17584, d51943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17584, d51943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17585 q = 1) (hb : d51944 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17585, d51944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17585, d51944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d17586 q = 1) (hb : d51945 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d17586, d51945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17586, d51945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17587 q = 1) (hb : d51946 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d17587, d51946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17587, d51946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d17588 q = 1) (hb : d51947 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d17588, d51947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17588, d51947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41470 (p : Pattern) (ha : d17596 p = 1) (hb : d52049 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17593 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17593, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17593, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17594 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17594, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17594, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17561 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17561, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17562 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17562, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17595 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17595, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17595, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17563 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17563, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d17596 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17596, d52049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17596, d52049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41471 (p : Pattern) (ha : d17602 p = 1) (hb : d52055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17597 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41470 q ha hb
    | true =>
      simp only [d17597, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41465 q ha hb
  have h2 (q : Pattern) (ha : d17598 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17599 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17565 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41465 q ha hb
    | true =>
      simp only [d17565, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17566 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17567 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17600 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17600, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17568 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17568, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17601 q = 1) (hb : d52054 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17601, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17601, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17602 q = 1) (hb : d52055 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17602, d52055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17602, d52055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41472 (p : Pattern) (ha : d17608 p = 1) (hb : d52061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17603 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41471 q ha hb
    | true =>
      simp only [d17603, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17604 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17571 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41466 q ha hb
    | true =>
      simp only [d17571, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17572 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17572, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17605 q = 1) (hb : d52058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17605, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17605, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17606 q = 1) (hb : d52059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17606, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17606, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17607 q = 1) (hb : d52060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17607, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17607, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17608 q = 1) (hb : d52061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17608, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17608, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41473 (p : Pattern) (ha : d52067 p = 1) (hb : d60563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17609 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41472 q ha hb
    | true =>
      simp only [d17609, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41467 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52063 q = 1) (hb : d60559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52063, d60559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52063, d60559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17577 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41467 q ha hb
    | true =>
      simp only [d17577, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17578 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17578, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d52064 q = 1) (hb : d60560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52064, d60560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52064, d60560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52065 q = 1) (hb : d60561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52065, d60561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52065, d60561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52066 q = 1) (hb : d60562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52066, d60562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52066, d60562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52067 q = 1) (hb : d60563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52067, d60563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52067, d60563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41474 (p : Pattern) (ha : d52073 p = 1) (hb : d60569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52043 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52068 q = 1) (hb : d60564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52068, d60564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52068, d60564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41473 q ha hb
  have h3 (q : Pattern) (ha : d52069 q = 1) (hb : d60565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52069, d60565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52069, d60565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d52070 q = 1) (hb : d60566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52070, d60566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52070, d60566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d52071 q = 1) (hb : d60567 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52071, d60567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52071, d60567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d52072 q = 1) (hb : d60568 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52072, d60568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52072, d60568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d52073 q = 1) (hb : d60569 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d60569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52073, d60569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41475 (p : Pattern) (ha : d17696 p = 1) (hb : d52209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17577 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41467 q ha hb
    | true =>
      simp only [d17577, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17692 q = 1) (hb : d52205 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17692, d52205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17692, d52205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17693 q = 1) (hb : d52206 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17693, d52206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17693, d52206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17694 q = 1) (hb : d52207 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17694, d52207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17694, d52207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17695 q = 1) (hb : d52208 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17695, d52208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17695, d52208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17696 q = 1) (hb : d52209 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17696, d52209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17696, d52209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41476 (p : Pattern) (ha : d17649 p = 1) (hb : d126912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17643 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17643, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17643, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17644 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17644, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17644, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17593 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17593, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17593, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17594 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17594, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17594, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17645 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17645, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17645, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12600 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d17646 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17646, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17647 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d17647, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d17561 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d17561, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d17562 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d17562, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d17648 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17648, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d17648, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d17649 q = 1) (hb : d126912 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17649, d126912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17649, d126912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41477 (p : Pattern) (ha : d17655 p = 1) (hb : d126918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17650 q = 1) (hb : d126913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41476 q ha hb
    | true =>
      simp only [d17650, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41470 q ha hb
  have h2 (q : Pattern) (ha : d17651 q = 1) (hb : d126914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17652 q = 1) (hb : d126915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17597 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41470 q ha hb
    | true =>
      simp only [d17597, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41465 q ha hb
  have h5 (q : Pattern) (ha : d17598 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17599 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17653 q = 1) (hb : d126916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17653, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17565 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41465 q ha hb
    | true =>
      simp only [d17565, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17566 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17567 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17600 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17600, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17654 q = 1) (hb : d126917 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17654, d126917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17654, d126917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17655 q = 1) (hb : d126918 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17655, d126918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17655, d126918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41478 (p : Pattern) (ha : d17661 p = 1) (hb : d126924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17656 q = 1) (hb : d126919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17656, d126919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41477 q ha hb
    | true =>
      simp only [d17656, d126919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17657 q = 1) (hb : d126920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17657, d126920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17657, d126920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17603 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41471 q ha hb
    | true =>
      simp only [d17603, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17604 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17658 q = 1) (hb : d126921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17658, d126921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17658, d126921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17659 q = 1) (hb : d126922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17659, d126922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17659, d126922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17660 q = 1) (hb : d126923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17660, d126923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17660, d126923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17661 q = 1) (hb : d126924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17661, d126924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17661, d126924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41479 (p : Pattern) (ha : d17684 p = 1) (hb : d74103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17603 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41471 q ha hb
    | true =>
      simp only [d17603, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17604 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17681 q = 1) (hb : d74100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17681, d74100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17681, d74100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17682 q = 1) (hb : d74101 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17682, d74101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17682, d74101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17683 q = 1) (hb : d74102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17683, d74102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17683, d74102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17684 q = 1) (hb : d74103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17684, d74103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17684, d74103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41480 (p : Pattern) (ha : d126930 p = 1) (hb : d129315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17662 q = 1) (hb : d126925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17662, d126925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41478 q ha hb
    | true =>
      simp only [d17662, d126925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41472 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d126926 q = 1) (hb : d129311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d126926, d129311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126926, d129311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17685 q = 1) (hb : d74104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17685, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41479 q ha hb
    | true =>
      simp only [d17685, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17686 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17686, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17686, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d126927 q = 1) (hb : d129312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126927, d129312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126927, d129312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d126928 q = 1) (hb : d129313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d126928, d129313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126928, d129313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126929 q = 1) (hb : d129314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d126929, d129314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126929, d129314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d126930 q = 1) (hb : d129315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126930, d129315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126930, d129315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41481 (p : Pattern) (ha : d126936 p = 1) (hb : d129321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126911 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126931 q = 1) (hb : d129316 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126931, d129316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126931, d129316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41480 q ha hb
  have h3 (q : Pattern) (ha : d17697 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17697, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41475 q ha hb
  have h4 (q : Pattern) (ha : d126932 q = 1) (hb : d129317 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126932, d129317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d126932, d129317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d126933 q = 1) (hb : d129318 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126933, d129318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d126933, d129318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d126934 q = 1) (hb : d129319 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126934, d129319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d126934, d129319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d126935 q = 1) (hb : d129320 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126935, d129320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126935, d129320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d126936 q = 1) (hb : d129321 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d126936, d129321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126936, d129321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41482 (p : Pattern) (ha : d126942 p = 1) (hb : d129327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17589 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d17589, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17589, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41469 q ha hb
  have h2 (q : Pattern) (ha : d17590 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d17590, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17590, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17591 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d17591, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17591, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17592 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d17592, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17592, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52074 q = 1) (hb : d60570 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d60570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52074, d60570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41474 q ha hb
  have h6 (q : Pattern) (ha : d52075 q = 1) (hb : d60571 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d60571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52075, d60571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52076 q = 1) (hb : d60572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d60572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52076, d60572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52077 q = 1) (hb : d60573 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d60573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52077, d60573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52078 q = 1) (hb : d60574 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d60574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52078, d60574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d126937 q = 1) (hb : d129322 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d126937, d129322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126937, d129322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41481 q ha hb
  have h11 (q : Pattern) (ha : d126938 q = 1) (hb : d129323 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d126938, d129323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126938, d129323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d126939 q = 1) (hb : d129324 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d126939, d129324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126939, d129324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d126940 q = 1) (hb : d129325 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d126940, d129325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126940, d129325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d126941 q = 1) (hb : d129326 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d126941, d129326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126941, d129326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d126942 q = 1) (hb : d129327 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d126942, d129327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d126942, d129327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41483 (p : Pattern) (ha : d17740 p = 1) (hb : d52387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17597 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41470 q ha hb
    | true =>
      simp only [d17597, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41465 q ha hb
  have h2 (q : Pattern) (ha : d17598 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17599 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17730 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17730, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17739 q = 1) (hb : d52386 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17739, d52386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17739, d52386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17740 q = 1) (hb : d52387 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17740, d52387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17740, d52387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41484 (p : Pattern) (ha : d17792 p = 1) (hb : d52398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17741 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41483 q ha hb
    | true =>
      simp only [d17741, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17742 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17742, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17789 q = 1) (hb : d52395 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17789, d52395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17789, d52395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17790 q = 1) (hb : d52396 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17790, d52396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17790, d52396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17791 q = 1) (hb : d52397 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17791, d52397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17791, d52397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17792 q = 1) (hb : d52398 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17792, d52398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17792, d52398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41485 (p : Pattern) (ha : d17798 p = 1) (hb : d52413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17793 q = 1) (hb : d52408 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17793, d52408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41484 q ha hb
    | true =>
      simp only [d17793, d52408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17794 q = 1) (hb : d52409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17794, d52409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17794, d52409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17795 q = 1) (hb : d52410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17795, d52410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17795, d52410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17796 q = 1) (hb : d52411 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17796, d52411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17796, d52411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17797 q = 1) (hb : d52412 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17797, d52412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17797, d52412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17798 q = 1) (hb : d52413 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17798, d52413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17798, d52413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41486 (p : Pattern) (ha : d17717 p = 1) (hb : d127053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17709 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17709, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17709, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17710 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17710, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17710, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16156 q = 1) (hb : d127047 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d127048 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16157, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101075 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17711 q = 1) (hb : d127049 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17711, d127049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17711, d127049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17712 q = 1) (hb : d127050 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17712, d127050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17712, d127050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17713 q = 1) (hb : d127051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17713, d127051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17713, d127051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h15 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12859 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d17714 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17714, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17715 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d17715, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h21 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12600 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d17646 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d17646, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d17647 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d17647, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d17716 q = 1) (hb : d127052 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17716, d127052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d17716, d127052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d17717 q = 1) (hb : d127053 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17717, d127053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17717, d127053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41487 (p : Pattern) (ha : d17721 p = 1) (hb : d127057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17646 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17646, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17647 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17647, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17561 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17561, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17562 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17562, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17648 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17648, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17648, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17563 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17563, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d17721 q = 1) (hb : d127057 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17721, d127057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17721, d127057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41488 (p : Pattern) (ha : d17727 p = 1) (hb : d127063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17718 q = 1) (hb : d127054 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17718, d127054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41486 q ha hb
    | true =>
      simp only [d17718, d127054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41476 q ha hb
  have h2 (q : Pattern) (ha : d17719 q = 1) (hb : d127055 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17719, d127055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17719, d127055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17720 q = 1) (hb : d127056 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17720, d127056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17720, d127056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17722 q = 1) (hb : d127058 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17722, d127058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41476 q ha hb
    | true =>
      simp only [d17722, d127058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41487 q ha hb
  have h5 (q : Pattern) (ha : d17723 q = 1) (hb : d127059 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17723, d127059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17723, d127059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17724 q = 1) (hb : d127060 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17724, d127060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17724, d127060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17725 q = 1) (hb : d127061 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17725, d127061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17725, d127061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17650 q = 1) (hb : d126913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41476 q ha hb
    | true =>
      simp only [d17650, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41470 q ha hb
  have h9 (q : Pattern) (ha : d17651 q = 1) (hb : d126914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17652 q = 1) (hb : d126915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17597 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41470 q ha hb
    | true =>
      simp only [d17597, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41465 q ha hb
  have h12 (q : Pattern) (ha : d17598 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17599 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17653 q = 1) (hb : d126916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17653, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17726 q = 1) (hb : d127062 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17726, d127062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17726, d127062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17727 q = 1) (hb : d127063 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17727, d127063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17727, d127063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41489 (p : Pattern) (ha : d17732 p = 1) (hb : d127067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17650 q = 1) (hb : d126913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41476 q ha hb
    | true =>
      simp only [d17650, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41470 q ha hb
  have h2 (q : Pattern) (ha : d17651 q = 1) (hb : d126914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17652 q = 1) (hb : d126915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17597 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41470 q ha hb
    | true =>
      simp only [d17597, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41465 q ha hb
  have h5 (q : Pattern) (ha : d17598 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17599 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17653 q = 1) (hb : d126916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17653, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17730 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17730, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17731 q = 1) (hb : d127066 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17731, d127066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17731, d127066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17732 q = 1) (hb : d127067 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17732, d127067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17732, d127067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41490 (p : Pattern) (ha : d17738 p = 1) (hb : d127073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17728 q = 1) (hb : d127064 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17728, d127064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41488 q ha hb
    | true =>
      simp only [d17728, d127064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17729 q = 1) (hb : d127065 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17729, d127065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17729, d127065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17733 q = 1) (hb : d127068 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, d127068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41489 q ha hb
    | true =>
      simp only [d17733, d127068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17734 q = 1) (hb : d127069 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, d127069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, d127069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17735 q = 1) (hb : d127070 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17735, d127070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17735, d127070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17736 q = 1) (hb : d127071 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17736, d127071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17736, d127071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17737 q = 1) (hb : d127072 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17737, d127072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17737, d127072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17738 q = 1) (hb : d127073 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17738, d127073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17738, d127073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41491 (p : Pattern) (ha : d17746 p = 1) (hb : d127077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17733 q = 1) (hb : d127068 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, d127068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41489 q ha hb
    | true =>
      simp only [d17733, d127068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17734 q = 1) (hb : d127069 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, d127069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, d127069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17741 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41483 q ha hb
    | true =>
      simp only [d17741, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17742 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17742, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17743 q = 1) (hb : d127074 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17743, d127074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17743, d127074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17744 q = 1) (hb : d127075 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17744, d127075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17744, d127075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17745 q = 1) (hb : d127076 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17745, d127076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17745, d127076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17746 q = 1) (hb : d127077 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17746, d127077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17746, d127077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41492 (p : Pattern) (ha : d17781 p = 1) (hb : d127084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17733 q = 1) (hb : d127068 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, d127068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41489 q ha hb
    | true =>
      simp only [d17733, d127068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17734 q = 1) (hb : d127069 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, d127069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, d127069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17778 q = 1) (hb : d127081 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17778, d127081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17778, d127081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17779 q = 1) (hb : d127082 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17779, d127082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17779, d127082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17780 q = 1) (hb : d127083 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17780, d127083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17780, d127083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17781 q = 1) (hb : d127084 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17781, d127084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17781, d127084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41493 (p : Pattern) (ha : d127090 p = 1) (hb : d129332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17747 q = 1) (hb : d127078 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17747, d127078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41490 q ha hb
    | true =>
      simp only [d17747, d127078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41491 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127079 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d127080 q = 1) (hb : d129328 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127080, d129328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127080, d129328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17782 q = 1) (hb : d127085 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17782, d127085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41492 q ha hb
    | true =>
      simp only [d17782, d127085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17783 q = 1) (hb : d127086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17783, d127086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17783, d127086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d127087 q = 1) (hb : d129329 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127087, d129329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127087, d129329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d127088 q = 1) (hb : d129330 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127088, d129330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127088, d129330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127089 q = 1) (hb : d129331 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127089, d129331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127089, d129331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127090 q = 1) (hb : d129332 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127090, d129332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127090, d129332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41494 (p : Pattern) (ha : d127096 p = 1) (hb : d129338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127091 q = 1) (hb : d129333 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127091, d129333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127091, d129333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41493 q ha hb
  have h3 (q : Pattern) (ha : d17799 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17799, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17799, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41485 q ha hb
  have h4 (q : Pattern) (ha : d127092 q = 1) (hb : d129334 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127092, d129334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127092, d129334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d127093 q = 1) (hb : d129335 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127093, d129335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127093, d129335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d127094 q = 1) (hb : d129336 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127094, d129336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127094, d129336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d127095 q = 1) (hb : d129337 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127095, d129337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127095, d129337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d127096 q = 1) (hb : d129338 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127096, d129338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127096, d129338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41495 (p : Pattern) (ha : d127102 p = 1) (hb : d129344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127097 q = 1) (hb : d129339 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127097, d129339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127097, d129339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41494 q ha hb
  have h2 (q : Pattern) (ha : d127098 q = 1) (hb : d129340 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127098, d129340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127098, d129340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127099 q = 1) (hb : d129341 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127099, d129341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127099, d129341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127100 q = 1) (hb : d129342 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127100, d129342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127100, d129342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127101 q = 1) (hb : d129343 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127101, d129343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127101, d129343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127102 q = 1) (hb : d129344 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127102, d129344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127102, d129344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41496 (p : Pattern) (ha : d17835 p = 1) (hb : d52600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17643 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17643, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17643, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17644 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17644, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17644, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17821 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17821, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17822 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17822, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17834 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17834, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17834, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17828 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17828, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d17835 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17835, d52600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17835, d52600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41497 (p : Pattern) (ha : d17839 p = 1) (hb : d52605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17821 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17821, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17822 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17822, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17828 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17828, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17839 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17839, d52605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17839, d52605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41498 (p : Pattern) (ha : d17858 p = 1) (hb : d52624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17840 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41496 q ha hb
    | true =>
      simp only [d17840, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41497 q ha hb
  have h2 (q : Pattern) (ha : d17841 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17842 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17848 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17848, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17857 q = 1) (hb : d52623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17857, d52623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17857, d52623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17858 q = 1) (hb : d52624 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17858, d52624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17858, d52624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41499 (p : Pattern) (ha : d17921 p = 1) (hb : d52635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17859 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41498 q ha hb
    | true =>
      simp only [d17859, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17860 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17860, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17918 q = 1) (hb : d52632 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17918, d52632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17918, d52632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17919 q = 1) (hb : d52633 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17919, d52633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17919, d52633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17920 q = 1) (hb : d52634 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17920, d52634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17920, d52634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17921 q = 1) (hb : d52635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17921, d52635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17921, d52635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
