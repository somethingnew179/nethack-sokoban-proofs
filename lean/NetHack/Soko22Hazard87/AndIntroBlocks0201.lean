import NetHack.Soko22Hazard87.AndIntroBlocks0200
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro50250 (p : Pattern) (ha : d108361 p = 1) (hb : d149390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108356 q = 1) (hb : d149385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108356, d149385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50249 q ha hb
    | true =>
      simp only [d108356, d149385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108357 q = 1) (hb : d149386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108357, d149386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108357, d149386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108358 q = 1) (hb : d149387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108358, d149387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108358, d149387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108296 q = 1) (hb : d149323 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108296, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50235 q ha hb
    | true =>
      simp only [d108296, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108297 q = 1) (hb : d149324 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108297, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108297, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108298 q = 1) (hb : d149325 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108298, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108298, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108359 q = 1) (hb : d149388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108359, d149388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108359, d149388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108299 q = 1) (hb : d149327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108299, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50236 q ha hb
    | true =>
      simp only [d108299, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108300 q = 1) (hb : d149328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108300, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108300, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108301 q = 1) (hb : d149329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108301, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108301, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108302 q = 1) (hb : d149330 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108302, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108302, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108360 q = 1) (hb : d149389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108360, d149389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108360, d149389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108361 q = 1) (hb : d149390 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108361, d149390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108361, d149390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50251 (p : Pattern) (ha : d108367 p = 1) (hb : d149396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108362 q = 1) (hb : d149391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108362, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50250 q ha hb
    | true =>
      simp only [d108362, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108363 q = 1) (hb : d149392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108363, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108363, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108306 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50237 q ha hb
    | true =>
      simp only [d108306, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108307 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108364 q = 1) (hb : d149393 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108364, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108364, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108365 q = 1) (hb : d149394 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108365, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108365, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108366 q = 1) (hb : d149395 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108366, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108366, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108367 q = 1) (hb : d149396 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108367, d149396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108367, d149396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50252 (p : Pattern) (ha : d74361 p = 1) (hb : d149326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22220 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
    | true =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22221 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22222 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22222, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22222, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22223 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22223, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22223, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22233 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46205 q ha hb
    | true =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22234 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22235 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22235, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22235, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22236 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22236, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22236, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22237 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22237, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22237, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74360 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74361 q = 1) (hb : d149326 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74361, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d74361, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50253 (p : Pattern) (ha : d108375 p = 1) (hb : d149333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108296 q = 1) (hb : d149323 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108296, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50235 q ha hb
    | true =>
      simp only [d108296, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108297 q = 1) (hb : d149324 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108297, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108297, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108298 q = 1) (hb : d149325 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108298, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108298, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108299 q = 1) (hb : d149327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108299, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50236 q ha hb
    | true =>
      simp only [d108299, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108300 q = 1) (hb : d149328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108300, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108300, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108301 q = 1) (hb : d149329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108301, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108301, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108302 q = 1) (hb : d149330 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108302, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108302, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108370 q = 1) (hb : d149327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108370, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50252 q ha hb
    | true =>
      simp only [d108370, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108371 q = 1) (hb : d149328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108371, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108371, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108372 q = 1) (hb : d149329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108372, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108372, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108373 q = 1) (hb : d149331 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108373, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108373, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108374 q = 1) (hb : d149332 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108374, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108374, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108375 q = 1) (hb : d149333 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108375, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108375, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50254 (p : Pattern) (ha : d108381 p = 1) (hb : d149402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108376 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108376, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50253 q ha hb
    | true =>
      simp only [d108376, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108377 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108377, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108377, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108378 q = 1) (hb : d149399 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108378, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108378, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108379 q = 1) (hb : d149400 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108379, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108379, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108380 q = 1) (hb : d149401 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108380, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108380, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108381 q = 1) (hb : d149402 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108381, d149402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108381, d149402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50255 (p : Pattern) (ha : d108387 p = 1) (hb : d149408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108343 q = 1) (hb : d149371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108343, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50245 q ha hb
    | true =>
      simp only [d108343, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50246 q ha hb
  have h2 (q : Pattern) (ha : d108344 q = 1) (hb : d149372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108344, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108344, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108345 q = 1) (hb : d149373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108345, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108345, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108346 q = 1) (hb : d149374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108346, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108346, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108353 q = 1) (hb : d149381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108353, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50247 q ha hb
    | true =>
      simp only [d108353, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50248 q ha hb
  have h6 (q : Pattern) (ha : d108354 q = 1) (hb : d149382 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108354, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108354, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108355 q = 1) (hb : d149383 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108355, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108355, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108368 q = 1) (hb : d149397 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108368, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50251 q ha hb
    | true =>
      simp only [d108368, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50239 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108320 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108369 q = 1) (hb : d149398 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108369, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108382 q = 1) (hb : d149403 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108382, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50254 q ha hb
    | true =>
      simp only [d108382, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108383 q = 1) (hb : d149404 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108383, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108383, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108384 q = 1) (hb : d149405 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108384, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108385 q = 1) (hb : d149406 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108385, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108386 q = 1) (hb : d149407 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108386, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108387 q = 1) (hb : d149408 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108387, d149408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108387, d149408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro50256 (p : Pattern) (ha : d108388 p = 1) (hb : d149409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50237 q ha hb
    | true =>
      simp only [d108306, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108310 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50238 q ha hb
    | true =>
      simp only [d108310, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108311 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d149340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108313 q = 1) (hb : d149341 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108313, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108313, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108339 q = 1) (hb : d149367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108339, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108339, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108388 q = 1) (hb : d149409 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108388, d149409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108388, d149409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50257 (p : Pattern) (ha : d108389 p = 1) (hb : d149410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108310 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50238 q ha hb
    | true =>
      simp only [d108310, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108311 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108316 q = 1) (hb : d149344 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108316, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108316, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108317 q = 1) (hb : d149345 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108317, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108317, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108341 q = 1) (hb : d149369 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108341, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108341, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108389 q = 1) (hb : d149410 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108389, d149410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108389, d149410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50258 (p : Pattern) (ha : d108394 p = 1) (hb : d149415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50237 q ha hb
    | true =>
      simp only [d108306, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108310 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50238 q ha hb
    | true =>
      simp only [d108310, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108311 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d149340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108347 q = 1) (hb : d149375 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108347, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108347, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108348 q = 1) (hb : d149376 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108348, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108348, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108394 q = 1) (hb : d149415 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108394, d149415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108394, d149415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50259 (p : Pattern) (ha : d108395 p = 1) (hb : d149416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108310 q = 1) (hb : d149338 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50238 q ha hb
    | true =>
      simp only [d108310, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108311 q = 1) (hb : d149339 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108316 q = 1) (hb : d149344 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108316, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108316, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108350 q = 1) (hb : d149378 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108350, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108350, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108351 q = 1) (hb : d149379 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108351, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108351, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108395 q = 1) (hb : d149416 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108395, d149416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108395, d149416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50260 (p : Pattern) (ha : d108399 p = 1) (hb : d149420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108362 q = 1) (hb : d149391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108362, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50250 q ha hb
    | true =>
      simp only [d108362, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108363 q = 1) (hb : d149392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108363, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108363, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108306 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50237 q ha hb
    | true =>
      simp only [d108306, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108307 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108364 q = 1) (hb : d149393 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108364, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108364, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108365 q = 1) (hb : d149394 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108365, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108365, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108366 q = 1) (hb : d149395 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108366, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108366, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108399 q = 1) (hb : d149420 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108399, d149420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108399, d149420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50261 (p : Pattern) (ha : d108402 p = 1) (hb : d149423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108376 q = 1) (hb : d149334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108376, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50253 q ha hb
    | true =>
      simp only [d108376, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108377 q = 1) (hb : d149335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108377, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108377, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108378 q = 1) (hb : d149399 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108378, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108378, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108379 q = 1) (hb : d149400 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108379, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108379, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108380 q = 1) (hb : d149401 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108380, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108380, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108402 q = 1) (hb : d149423 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108402, d149423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108402, d149423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50262 (p : Pattern) (ha : d108408 p = 1) (hb : d149429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108343 q = 1) (hb : d149371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108343, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50245 q ha hb
    | true =>
      simp only [d108343, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50246 q ha hb
  have h2 (q : Pattern) (ha : d108344 q = 1) (hb : d149372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108344, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108344, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108345 q = 1) (hb : d149373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108345, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108345, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108346 q = 1) (hb : d149374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108346, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108346, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108353 q = 1) (hb : d149381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108353, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50247 q ha hb
    | true =>
      simp only [d108353, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50248 q ha hb
  have h6 (q : Pattern) (ha : d108354 q = 1) (hb : d149382 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108354, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108354, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108355 q = 1) (hb : d149383 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108355, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108355, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108368 q = 1) (hb : d149397 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108368, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50251 q ha hb
    | true =>
      simp only [d108368, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50239 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108320 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108369 q = 1) (hb : d149398 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108369, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108382 q = 1) (hb : d149403 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108382, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50254 q ha hb
    | true =>
      simp only [d108382, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108383 q = 1) (hb : d149404 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108383, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108383, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108384 q = 1) (hb : d149405 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108384, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108385 q = 1) (hb : d149406 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108385, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108386 q = 1) (hb : d149407 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108386, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108390 q = 1) (hb : d149411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108390, d149411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50256 q ha hb
    | true =>
      simp only [d108390, d149411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50257 q ha hb
  have h17 (q : Pattern) (ha : d108391 q = 1) (hb : d149412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108391, d149412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108391, d149412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108392 q = 1) (hb : d149413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108392, d149413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108392, d149413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d108393 q = 1) (hb : d149414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108393, d149414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108393, d149414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108396 q = 1) (hb : d149417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108396, d149417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50258 q ha hb
    | true =>
      simp only [d108396, d149417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50259 q ha hb
  have h21 (q : Pattern) (ha : d108397 q = 1) (hb : d149418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108397, d149418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108397, d149418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d108398 q = 1) (hb : d149419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108398, d149419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108398, d149419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108400 q = 1) (hb : d149421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108400, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50260 q ha hb
    | true =>
      simp only [d108400, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50242 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d108330 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d108401 q = 1) (hb : d149422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108401, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d108403 q = 1) (hb : d149424 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108403, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50261 q ha hb
    | true =>
      simp only [d108403, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d108404 q = 1) (hb : d149425 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108404, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108404, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d108405 q = 1) (hb : d149426 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108405, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108406 q = 1) (hb : d149427 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108406, d149427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108406, d149427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d108407 q = 1) (hb : d149428 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108407, d149428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108407, d149428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108408 q = 1) (hb : d149429 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108408, d149429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108408, d149429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro50263 (p : Pattern) (ha : d108415 p = 1) (hb : d149436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108320 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50239 q ha hb
    | true =>
      simp only [d108320, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50240 q ha hb
  have h2 (q : Pattern) (ha : d108321 q = 1) (hb : d149349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108321, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108321, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108322 q = 1) (hb : d149350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108322, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108322, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108323 q = 1) (hb : d149351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108323, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108323, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108324 q = 1) (hb : d149352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108324, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108324, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108410 q = 1) (hb : d149431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108410, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50240 q ha hb
    | true =>
      simp only [d108410, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108411 q = 1) (hb : d149432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108411, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108411, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108412 q = 1) (hb : d149433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108412, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108412, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108413 q = 1) (hb : d149434 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108413, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108413, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108414 q = 1) (hb : d149435 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108414, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108414, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108415 q = 1) (hb : d149436 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108415, d149436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108415, d149436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50264 (p : Pattern) (ha : d108421 p = 1) (hb : d149442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108410 q = 1) (hb : d149431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108410, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50240 q ha hb
    | true =>
      simp only [d108410, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108411 q = 1) (hb : d149432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108411, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108411, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108412 q = 1) (hb : d149433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108412, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108412, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108413 q = 1) (hb : d149434 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108413, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108413, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108414 q = 1) (hb : d149435 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108414, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108414, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108416 q = 1) (hb : d149437 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108416, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50243 q ha hb
    | true =>
      simp only [d108416, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108417 q = 1) (hb : d149438 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108417, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108417, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108418 q = 1) (hb : d149439 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108418, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108418, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108419 q = 1) (hb : d149440 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108419, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108419, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108420 q = 1) (hb : d149441 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108420, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108420, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108421 q = 1) (hb : d149442 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108421, d149442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108421, d149442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50265 (p : Pattern) (ha : d108428 p = 1) (hb : d149449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108400 q = 1) (hb : d149421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108400, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50260 q ha hb
    | true =>
      simp only [d108400, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50242 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108401 q = 1) (hb : d149422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108401, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108403 q = 1) (hb : d149424 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108403, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50261 q ha hb
    | true =>
      simp only [d108403, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108404 q = 1) (hb : d149425 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108404, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108404, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108405 q = 1) (hb : d149426 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108405, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108426 q = 1) (hb : d149447 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108426, d149447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108426, d149447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108427 q = 1) (hb : d149448 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108427, d149448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108427, d149448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108428 q = 1) (hb : d149449 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108428, d149449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108428, d149449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50266 (p : Pattern) (ha : d108430 p = 1) (hb : d149451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108416 q = 1) (hb : d149437 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108416, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50243 q ha hb
    | true =>
      simp only [d108416, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108417 q = 1) (hb : d149438 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108417, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108417, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108418 q = 1) (hb : d149439 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108418, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108418, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108419 q = 1) (hb : d149440 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108419, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108419, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108420 q = 1) (hb : d149441 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108420, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108420, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108430 q = 1) (hb : d149451 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108430, d149451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108430, d149451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50267 (p : Pattern) (ha : d53193 p = 1) (hb : d149457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22497 q = 1) (hb : d53179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22497, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22497, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46225 q ha hb
  have h2 (q : Pattern) (ha : d22313 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22313, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46225 q ha hb
    | true =>
      simp only [d22313, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22498 q = 1) (hb : d53180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22498, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22498, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22314 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22314, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22314, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22499 q = 1) (hb : d53181 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22499, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22499, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22500 q = 1) (hb : d53182 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22500, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22500, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17004 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
  have h8 (q : Pattern) (ha : d10036 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
    | true =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17005 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17005, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10038 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17006 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17006, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17007 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17007, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22501 q = 1) (hb : d53187 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22501, d53187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22501, d53187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53193 q = 1) (hb : d149457 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53193, d149457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d53193, d149457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50268 (p : Pattern) (ha : d53199 p = 1) (hb : d149461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17004 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
  have h2 (q : Pattern) (ha : d10036 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
    | true =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17005 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17005, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10038 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17006 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17006, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17007 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17007, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22508 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
  have h8 (q : Pattern) (ha : d22220 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
    | true =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22509 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22221 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22510 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22511 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22512 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22512, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22512, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53199 q = 1) (hb : d149461 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53199, d149461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d53199, d149461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50269 (p : Pattern) (ha : d53204 p = 1) (hb : d149466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22508 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
  have h2 (q : Pattern) (ha : d22220 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
    | true =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22509 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22221 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22510 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22511 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22529 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46205 q ha hb
  have h8 (q : Pattern) (ha : d22233 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46205 q ha hb
    | true =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22530 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22530, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22234 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22531 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22531, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22532 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22532, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22533 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22533, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22533, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53204 q = 1) (hb : d149466 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53204, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d53204, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50270 (p : Pattern) (ha : d108448 p = 1) (hb : d149472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108436 q = 1) (hb : d149458 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108436, d149458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50267 q ha hb
    | true =>
      simp only [d108436, d149458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108437 q = 1) (hb : d149459 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108437, d149459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108437, d149459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108438 q = 1) (hb : d149460 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108438, d149460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108438, d149460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108439 q = 1) (hb : d149462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108439, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50268 q ha hb
    | true =>
      simp only [d108439, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108440 q = 1) (hb : d149463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108440, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108440, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108441 q = 1) (hb : d149464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108441, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108441, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108442 q = 1) (hb : d149465 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108442, d149465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108442, d149465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108443 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108443, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50269 q ha hb
    | true =>
      simp only [d108443, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108444 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108444, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108444, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108445 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108445, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108445, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108446 q = 1) (hb : d149470 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108446, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108446, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108447 q = 1) (hb : d149471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108447, d149471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108447, d149471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108448 q = 1) (hb : d149472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108448, d149472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108448, d149472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50271 (p : Pattern) (ha : d108453 p = 1) (hb : d149477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108439 q = 1) (hb : d149462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108439, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50268 q ha hb
    | true =>
      simp only [d108439, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108440 q = 1) (hb : d149463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108440, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108440, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108441 q = 1) (hb : d149464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108441, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108441, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108443 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108443, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50269 q ha hb
    | true =>
      simp only [d108443, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108444 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108444, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108444, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108445 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108445, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108445, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108446 q = 1) (hb : d149470 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108446, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108446, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108451 q = 1) (hb : d149475 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108451, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108451, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108452 q = 1) (hb : d149476 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108452, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108452, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108453 q = 1) (hb : d149477 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108453, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108453, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50272 (p : Pattern) (ha : d108459 p = 1) (hb : d149483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108449 q = 1) (hb : d149473 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108449, d149473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50270 q ha hb
    | true =>
      simp only [d108449, d149473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108450 q = 1) (hb : d149474 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108450, d149474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108450, d149474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108454 q = 1) (hb : d149478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108454, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50271 q ha hb
    | true =>
      simp only [d108454, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108455 q = 1) (hb : d149479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108455, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108455, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108456 q = 1) (hb : d149480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108456, d149480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108456, d149480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108457 q = 1) (hb : d149481 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108457, d149481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108457, d149481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108458 q = 1) (hb : d149482 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108458, d149482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108458, d149482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108459 q = 1) (hb : d149483 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108459, d149483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108459, d149483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50273 (p : Pattern) (ha : d108461 p = 1) (hb : d149485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108443 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108443, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50269 q ha hb
    | true =>
      simp only [d108443, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108444 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108444, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108444, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108445 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108445, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108445, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108451 q = 1) (hb : d149475 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108451, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108451, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108460 q = 1) (hb : d149484 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108460, d149484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108460, d149484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108461 q = 1) (hb : d149485 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108461, d149485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108461, d149485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50274 (p : Pattern) (ha : d108467 p = 1) (hb : d149491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108454 q = 1) (hb : d149478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108454, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50271 q ha hb
    | true =>
      simp only [d108454, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108455 q = 1) (hb : d149479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108455, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108455, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108462 q = 1) (hb : d149486 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108462, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50273 q ha hb
    | true =>
      simp only [d108462, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108463 q = 1) (hb : d149487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108463, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108463, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108464 q = 1) (hb : d149488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108464, d149488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108464, d149488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108465 q = 1) (hb : d149489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108465, d149489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108465, d149489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108466 q = 1) (hb : d149490 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108466, d149490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108466, d149490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108467 q = 1) (hb : d149491 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108467, d149491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108467, d149491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50275 (p : Pattern) (ha : d74405 p = 1) (hb : d149466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22508 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
  have h2 (q : Pattern) (ha : d22220 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
    | true =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22509 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22221 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22510 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22511 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22529 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46205 q ha hb
  have h8 (q : Pattern) (ha : d22233 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46205 q ha hb
    | true =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22530 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22530, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22234 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22531 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22531, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22532 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22532, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22533 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22533, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22533, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74404 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74405 q = 1) (hb : d149466 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74405, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d74405, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50276 (p : Pattern) (ha : d108480 p = 1) (hb : d149477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108439 q = 1) (hb : d149462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108439, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50268 q ha hb
    | true =>
      simp only [d108439, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108440 q = 1) (hb : d149463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108440, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108440, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108441 q = 1) (hb : d149464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108441, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108441, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108443 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108443, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50269 q ha hb
    | true =>
      simp only [d108443, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108444 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108444, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108444, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108445 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108445, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108445, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108446 q = 1) (hb : d149470 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108446, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108446, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108475 q = 1) (hb : d149467 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108475, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50275 q ha hb
    | true =>
      simp only [d108475, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108476 q = 1) (hb : d149468 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108476, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108476, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108477 q = 1) (hb : d149469 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108477, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108477, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108478 q = 1) (hb : d149475 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108478, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108478, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108479 q = 1) (hb : d149476 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108479, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108479, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108480 q = 1) (hb : d149477 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108480, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108480, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50277 (p : Pattern) (ha : d108486 p = 1) (hb : d149497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108481 q = 1) (hb : d149478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108481, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50276 q ha hb
    | true =>
      simp only [d108481, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108482 q = 1) (hb : d149479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108482, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108482, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108483 q = 1) (hb : d149494 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108483, d149494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108483, d149494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108484 q = 1) (hb : d149495 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108484, d149495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108484, d149495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108485 q = 1) (hb : d149496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108485, d149496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108485, d149496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108486 q = 1) (hb : d149497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108486, d149497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108486, d149497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50278 (p : Pattern) (ha : d108492 p = 1) (hb : d149503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108468 q = 1) (hb : d149492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108468, d149492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50272 q ha hb
    | true =>
      simp only [d108468, d149492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50274 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108474 q = 1) (hb : d149493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108474, d149493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108474, d149493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108487 q = 1) (hb : d149498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108487, d149498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50277 q ha hb
    | true =>
      simp only [d108487, d149498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108488 q = 1) (hb : d149499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108488, d149499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108488, d149499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108489 q = 1) (hb : d149500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108489, d149500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108489, d149500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108490 q = 1) (hb : d149501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108490, d149501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108490, d149501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108491 q = 1) (hb : d149502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108491, d149502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108491, d149502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108492 q = 1) (hb : d149503 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108492, d149503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108492, d149503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50279 (p : Pattern) (ha : d108472 p = 1) (hb : d149508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108462 q = 1) (hb : d149486 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108462, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50273 q ha hb
    | true =>
      simp only [d108462, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108463 q = 1) (hb : d149487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108463, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108463, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108469 q = 1) (hb : d149505 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108469, d149505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108469, d149505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108470 q = 1) (hb : d149506 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108470, d149506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108470, d149506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108471 q = 1) (hb : d149507 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108471, d149507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108471, d149507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108472 q = 1) (hb : d149508 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108472, d149508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108472, d149508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50280 (p : Pattern) (ha : d108499 p = 1) (hb : d149514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108494 q = 1) (hb : d149509 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108494, d149509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50279 q ha hb
    | true =>
      simp only [d108494, d149509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108495 q = 1) (hb : d149510 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108495, d149510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108495, d149510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108496 q = 1) (hb : d149511 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108496, d149511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108496, d149511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108497 q = 1) (hb : d149512 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108497, d149512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108497, d149512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108498 q = 1) (hb : d149513 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108498, d149513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108498, d149513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108499 q = 1) (hb : d149514 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108499, d149514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108499, d149514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50281 (p : Pattern) (ha : d108505 p = 1) (hb : d149520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108326 q = 1) (hb : d149354 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108326, d149354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108326, d149354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50241 q ha hb
  have h2 (q : Pattern) (ha : d108327 q = 1) (hb : d149355 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108327, d149355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108327, d149355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108336 q = 1) (hb : d149364 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108336, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50241 q ha hb
    | true =>
      simp only [d108336, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50244 q ha hb
  have h4 (q : Pattern) (ha : d108337 q = 1) (hb : d149365 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108337, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108337, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108338 q = 1) (hb : d149366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108338, d149366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108338, d149366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108409 q = 1) (hb : d149430 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108409, d149430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50255 q ha hb
    | true =>
      simp only [d108409, d149430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50262 q ha hb
  have h7 (q : Pattern) (ha : d108422 q = 1) (hb : d149443 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108422, d149443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50263 q ha hb
    | true =>
      simp only [d108422, d149443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50264 q ha hb
  have h8 (q : Pattern) (ha : d108423 q = 1) (hb : d149444 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108423, d149444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108423, d149444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108424 q = 1) (hb : d149445 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108424, d149445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108424, d149445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d108425 q = 1) (hb : d149446 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108425, d149446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108425, d149446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108429 q = 1) (hb : d149450 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108429, d149450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108429, d149450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50265 q ha hb
  have h12 (q : Pattern) (ha : d108431 q = 1) (hb : d149452 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108431, d149452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108431, d149452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50266 q ha hb
  have h13 (q : Pattern) (ha : d108432 q = 1) (hb : d149453 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108432, d149453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108432, d149453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108433 q = 1) (hb : d149454 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108433, d149454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108433, d149454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d108434 q = 1) (hb : d149455 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108434, d149455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108434, d149455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d108435 q = 1) (hb : d149456 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108435, d149456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108435, d149456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108493 q = 1) (hb : d149504 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108493, d149504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108493, d149504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50278 q ha hb
  have h18 (q : Pattern) (ha : d108500 q = 1) (hb : d149515 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108500, d149515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108500, d149515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50280 q ha hb
  have h19 (q : Pattern) (ha : d108501 q = 1) (hb : d149516 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108501, d149516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108501, d149516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108502 q = 1) (hb : d149517 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108502, d149517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108502, d149517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108503 q = 1) (hb : d149518 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108503, d149518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108503, d149518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108504 q = 1) (hb : d149519 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108504, d149519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108504, d149519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108505 q = 1) (hb : d149520 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108505, d149520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108505, d149520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro50282 (p : Pattern) (ha : d108511 p = 1) (hb : d149526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108506 q = 1) (hb : d149521 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108506, d149521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108506, d149521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50281 q ha hb
  have h2 (q : Pattern) (ha : d108507 q = 1) (hb : d149522 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108507, d149522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108507, d149522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108508 q = 1) (hb : d149523 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108508, d149523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108508, d149523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108509 q = 1) (hb : d149524 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108509, d149524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108509, d149524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108510 q = 1) (hb : d149525 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108510, d149525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108510, d149525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108511 q = 1) (hb : d149526 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108511, d149526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108511, d149526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50283 (p : Pattern) (ha : d53349 p = 1) (hb : d149531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17225 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17226 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17153 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17154 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22685 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22685, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22685, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53349 q = 1) (hb : d149531 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53349, d149531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d53349, d149531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50284 (p : Pattern) (ha : d53351 p = 1) (hb : d149535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17153 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17154 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22688 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
    | true =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22689 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22690 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22691 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22691, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22692 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22692, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22692, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53351 q = 1) (hb : d149535 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53351, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d53351, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50285 (p : Pattern) (ha : d108525 p = 1) (hb : d149542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108516 q = 1) (hb : d149532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108516, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50283 q ha hb
    | true =>
      simp only [d108516, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108517 q = 1) (hb : d149533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108517, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108517, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108518 q = 1) (hb : d149534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108518, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108518, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108519 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108519, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50284 q ha hb
    | true =>
      simp only [d108519, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108520 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108520, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108520, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108521 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108521, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108521, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108522 q = 1) (hb : d149539 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108522, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108522, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108523 q = 1) (hb : d149540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108523, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108523, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108524 q = 1) (hb : d149541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108524, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108524, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108525 q = 1) (hb : d149542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108525, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108525, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50286 (p : Pattern) (ha : d108529 p = 1) (hb : d149546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108519 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108519, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50284 q ha hb
    | true =>
      simp only [d108519, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108520 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108520, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108520, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108521 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108521, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108521, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108523 q = 1) (hb : d149540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108523, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108523, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108528 q = 1) (hb : d149545 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108528, d149545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108528, d149545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108529 q = 1) (hb : d149546 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108529, d149546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108529, d149546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50287 (p : Pattern) (ha : d108535 p = 1) (hb : d149552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50285 q ha hb
    | true =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d149550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108534 q = 1) (hb : d149551 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108534, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108534, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108535 q = 1) (hb : d149552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108535, d149552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108535, d149552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50288 (p : Pattern) (ha : d108539 p = 1) (hb : d149556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108537 q = 1) (hb : d149554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108537, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108537, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108538 q = 1) (hb : d149555 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108538, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108538, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108539 q = 1) (hb : d149556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108539, d149556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108539, d149556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50289 (p : Pattern) (ha : d108545 p = 1) (hb : d149562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108540 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50287 q ha hb
    | true =>
      simp only [d108540, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50288 q ha hb
  have h2 (q : Pattern) (ha : d108541 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108541, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108541, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108542 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108542, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108542, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108543 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108543, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108543, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108544 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108544, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108544, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108545 q = 1) (hb : d149562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108545, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108545, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50290 (p : Pattern) (ha : d108548 p = 1) (hb : d149565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50285 q ha hb
    | true =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d149550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108534 q = 1) (hb : d149551 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108534, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108534, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108548 q = 1) (hb : d149565 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108548, d149565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108548, d149565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50291 (p : Pattern) (ha : d108549 p = 1) (hb : d149566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108537 q = 1) (hb : d149554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108537, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108537, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108538 q = 1) (hb : d149555 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108538, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108538, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108549 q = 1) (hb : d149566 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108549, d149566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108549, d149566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50292 (p : Pattern) (ha : d108555 p = 1) (hb : d149572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108540 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50287 q ha hb
    | true =>
      simp only [d108540, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50288 q ha hb
  have h2 (q : Pattern) (ha : d108541 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108541, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108541, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108542 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108542, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108542, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108543 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108543, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108543, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108544 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108544, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108544, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108550 q = 1) (hb : d149567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108550, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50290 q ha hb
    | true =>
      simp only [d108550, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50291 q ha hb
  have h7 (q : Pattern) (ha : d108551 q = 1) (hb : d149568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108551, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108551, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108552 q = 1) (hb : d149569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108552, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108552, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108553 q = 1) (hb : d149570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108553, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108553, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108554 q = 1) (hb : d149571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108554, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108554, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108555 q = 1) (hb : d149572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108555, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108555, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50293 (p : Pattern) (ha : d108560 p = 1) (hb : d149577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50285 q ha hb
    | true =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d149550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108559 q = 1) (hb : d149576 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108559, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108559, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108560 q = 1) (hb : d149577 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108560, d149577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108560, d149577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50294 (p : Pattern) (ha : d108562 p = 1) (hb : d149579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108537 q = 1) (hb : d149554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108537, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108537, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108561 q = 1) (hb : d149578 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108561, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108561, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108562 q = 1) (hb : d149579 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108562, d149579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108562, d149579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50295 (p : Pattern) (ha : d108569 p = 1) (hb : d149586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50285 q ha hb
    | true =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108567 q = 1) (hb : d149584 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108567, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108567, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108568 q = 1) (hb : d149585 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108568, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108568, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108569 q = 1) (hb : d149586 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108569, d149586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108569, d149586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50296 (p : Pattern) (ha : d108572 p = 1) (hb : d149589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108570 q = 1) (hb : d149587 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108570, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108570, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108571 q = 1) (hb : d149588 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108571, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108571, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108572 q = 1) (hb : d149589 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108572, d149589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108572, d149589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50297 (p : Pattern) (ha : d53428 p = 1) (hb : d149593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53426 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17225 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17226 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22767 q = 1) (hb : d53427 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22767, d53427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22767, d53427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53428 q = 1) (hb : d149593 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53428, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53428, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro50298 (p : Pattern) (ha : d108581 p = 1) (hb : d149599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108576 q = 1) (hb : d149594 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108576, d149594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50297 q ha hb
    | true =>
      simp only [d108576, d149594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108577 q = 1) (hb : d149595 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108577, d149595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108577, d149595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108578 q = 1) (hb : d149596 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108578, d149596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108578, d149596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108516 q = 1) (hb : d149532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108516, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50283 q ha hb
    | true =>
      simp only [d108516, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108517 q = 1) (hb : d149533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108517, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108517, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108518 q = 1) (hb : d149534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108518, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108518, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108579 q = 1) (hb : d149597 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108579, d149597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108579, d149597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108519 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108519, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50284 q ha hb
    | true =>
      simp only [d108519, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108520 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108520, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108520, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108521 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108521, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108521, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108522 q = 1) (hb : d149539 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108522, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108522, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108580 q = 1) (hb : d149598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108580, d149598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108580, d149598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108581 q = 1) (hb : d149599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108581, d149599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108581, d149599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50299 (p : Pattern) (ha : d108587 p = 1) (hb : d149605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108582 q = 1) (hb : d149600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108582, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50298 q ha hb
    | true =>
      simp only [d108582, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108583 q = 1) (hb : d149601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108583, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108583, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108526 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50285 q ha hb
    | true =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108527 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108584 q = 1) (hb : d149602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108584, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108584, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108585 q = 1) (hb : d149603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108585, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108585, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108586 q = 1) (hb : d149604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108586, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108586, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108587 q = 1) (hb : d149605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108587, d149605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108587, d149605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50300 (p : Pattern) (ha : d74452 p = 1) (hb : d149535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17153 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17154 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22688 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
    | true =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22689 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22690 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22691 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22691, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22692 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22692, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22692, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74451 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74452 q = 1) (hb : d149535 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74452, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d74452, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50301 (p : Pattern) (ha : d108595 p = 1) (hb : d149542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108516 q = 1) (hb : d149532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108516, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50283 q ha hb
    | true =>
      simp only [d108516, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108517 q = 1) (hb : d149533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108517, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108517, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108518 q = 1) (hb : d149534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108518, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108518, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108519 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108519, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50284 q ha hb
    | true =>
      simp only [d108519, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108520 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108520, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108520, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108521 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108521, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108521, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108522 q = 1) (hb : d149539 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108522, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108522, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108590 q = 1) (hb : d149536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108590, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50300 q ha hb
    | true =>
      simp only [d108590, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108591 q = 1) (hb : d149537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108591, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108591, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108592 q = 1) (hb : d149538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108592, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108592, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108593 q = 1) (hb : d149540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108593, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108593, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108594 q = 1) (hb : d149541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108594, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108594, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108595 q = 1) (hb : d149542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108595, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108595, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50302 (p : Pattern) (ha : d108601 p = 1) (hb : d149611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108596 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108596, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50301 q ha hb
    | true =>
      simp only [d108596, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108597 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108597, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108597, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108598 q = 1) (hb : d149608 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108598, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108598, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108599 q = 1) (hb : d149609 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108599, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108599, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108600 q = 1) (hb : d149610 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108600, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108600, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108601 q = 1) (hb : d149611 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108601, d149611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108601, d149611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50303 (p : Pattern) (ha : d108607 p = 1) (hb : d149617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108563 q = 1) (hb : d149580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108563, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50293 q ha hb
    | true =>
      simp only [d108563, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50294 q ha hb
  have h2 (q : Pattern) (ha : d108564 q = 1) (hb : d149581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108564, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108564, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108565 q = 1) (hb : d149582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108565, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108565, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108566 q = 1) (hb : d149583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108566, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108566, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108573 q = 1) (hb : d149590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108573, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50295 q ha hb
    | true =>
      simp only [d108573, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50296 q ha hb
  have h6 (q : Pattern) (ha : d108574 q = 1) (hb : d149591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108574, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108574, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108575 q = 1) (hb : d149592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108575, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108575, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108588 q = 1) (hb : d149606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108588, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50299 q ha hb
    | true =>
      simp only [d108588, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50287 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108540 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108589 q = 1) (hb : d149607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108589, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108602 q = 1) (hb : d149612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108602, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50302 q ha hb
    | true =>
      simp only [d108602, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108603 q = 1) (hb : d149613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108603, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108603, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108604 q = 1) (hb : d149614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108604, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108605 q = 1) (hb : d149615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108605, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108606 q = 1) (hb : d149616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108606, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108607 q = 1) (hb : d149617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108607, d149617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108607, d149617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro50304 (p : Pattern) (ha : d108608 p = 1) (hb : d149618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50285 q ha hb
    | true =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d149550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108559 q = 1) (hb : d149576 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108559, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108559, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108608 q = 1) (hb : d149618 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108608, d149618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108608, d149618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50305 (p : Pattern) (ha : d108609 p = 1) (hb : d149619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108537 q = 1) (hb : d149554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108537, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108537, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108561 q = 1) (hb : d149578 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108561, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108561, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108609 q = 1) (hb : d149619 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108609, d149619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108609, d149619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50306 (p : Pattern) (ha : d108614 p = 1) (hb : d149624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50285 q ha hb
    | true =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d149549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108567 q = 1) (hb : d149584 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108567, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108567, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108568 q = 1) (hb : d149585 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108568, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108568, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108614 q = 1) (hb : d149624 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108614, d149624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108614, d149624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50307 (p : Pattern) (ha : d108615 p = 1) (hb : d149625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d149547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50286 q ha hb
    | true =>
      simp only [d108530, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d149548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d149553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108570 q = 1) (hb : d149587 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108570, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108570, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108571 q = 1) (hb : d149588 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108571, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108571, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108615 q = 1) (hb : d149625 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108615, d149625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108615, d149625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50308 (p : Pattern) (ha : d108619 p = 1) (hb : d149629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108582 q = 1) (hb : d149600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108582, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50298 q ha hb
    | true =>
      simp only [d108582, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108583 q = 1) (hb : d149601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108583, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108583, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108526 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50285 q ha hb
    | true =>
      simp only [d108526, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108527 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108584 q = 1) (hb : d149602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108584, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108584, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108585 q = 1) (hb : d149603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108585, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108585, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108586 q = 1) (hb : d149604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108586, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108586, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108619 q = 1) (hb : d149629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108619, d149629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108619, d149629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50309 (p : Pattern) (ha : d108622 p = 1) (hb : d149632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108596 q = 1) (hb : d149543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108596, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50301 q ha hb
    | true =>
      simp only [d108596, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108597 q = 1) (hb : d149544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108597, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108597, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108598 q = 1) (hb : d149608 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108598, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108598, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108599 q = 1) (hb : d149609 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108599, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108599, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108600 q = 1) (hb : d149610 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108600, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108600, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108622 q = 1) (hb : d149632 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108622, d149632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108622, d149632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50310 (p : Pattern) (ha : d108628 p = 1) (hb : d149638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108563 q = 1) (hb : d149580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108563, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50293 q ha hb
    | true =>
      simp only [d108563, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50294 q ha hb
  have h2 (q : Pattern) (ha : d108564 q = 1) (hb : d149581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108564, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108564, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108565 q = 1) (hb : d149582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108565, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108565, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108566 q = 1) (hb : d149583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108566, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108566, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108573 q = 1) (hb : d149590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108573, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50295 q ha hb
    | true =>
      simp only [d108573, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50296 q ha hb
  have h6 (q : Pattern) (ha : d108574 q = 1) (hb : d149591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108574, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108574, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108575 q = 1) (hb : d149592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108575, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108575, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108588 q = 1) (hb : d149606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108588, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50299 q ha hb
    | true =>
      simp only [d108588, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50287 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108540 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108589 q = 1) (hb : d149607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108589, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108602 q = 1) (hb : d149612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108602, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50302 q ha hb
    | true =>
      simp only [d108602, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108603 q = 1) (hb : d149613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108603, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108603, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108604 q = 1) (hb : d149614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108604, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108605 q = 1) (hb : d149615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108605, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108606 q = 1) (hb : d149616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108606, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108610 q = 1) (hb : d149620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108610, d149620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50304 q ha hb
    | true =>
      simp only [d108610, d149620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50305 q ha hb
  have h17 (q : Pattern) (ha : d108611 q = 1) (hb : d149621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108611, d149621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108611, d149621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108612 q = 1) (hb : d149622 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108612, d149622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108612, d149622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d108613 q = 1) (hb : d149623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108613, d149623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108613, d149623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108616 q = 1) (hb : d149626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108616, d149626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50306 q ha hb
    | true =>
      simp only [d108616, d149626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50307 q ha hb
  have h21 (q : Pattern) (ha : d108617 q = 1) (hb : d149627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108617, d149627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108617, d149627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d108618 q = 1) (hb : d149628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108618, d149628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108618, d149628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108620 q = 1) (hb : d149630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108620, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50308 q ha hb
    | true =>
      simp only [d108620, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50290 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d108550 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d108621 q = 1) (hb : d149631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108621, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d108623 q = 1) (hb : d149633 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108623, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50309 q ha hb
    | true =>
      simp only [d108623, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d108624 q = 1) (hb : d149634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108624, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108624, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d108625 q = 1) (hb : d149635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108625, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108626 q = 1) (hb : d149636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108626, d149636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108626, d149636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d108627 q = 1) (hb : d149637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108627, d149637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108627, d149637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108628 q = 1) (hb : d149638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108628, d149638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108628, d149638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro50311 (p : Pattern) (ha : d108635 p = 1) (hb : d149645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108540 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50287 q ha hb
    | true =>
      simp only [d108540, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50288 q ha hb
  have h2 (q : Pattern) (ha : d108541 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108541, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108541, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108542 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108542, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108542, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108543 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108543, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108543, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108544 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108544, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108544, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108630 q = 1) (hb : d149640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108630, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50288 q ha hb
    | true =>
      simp only [d108630, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108631 q = 1) (hb : d149641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108631, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108631, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108632 q = 1) (hb : d149642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108632, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108632, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108633 q = 1) (hb : d149643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108633, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108633, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108634 q = 1) (hb : d149644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108634, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108634, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108635 q = 1) (hb : d149645 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108635, d149645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108635, d149645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50312 (p : Pattern) (ha : d108641 p = 1) (hb : d149651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108630 q = 1) (hb : d149640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108630, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50288 q ha hb
    | true =>
      simp only [d108630, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108631 q = 1) (hb : d149641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108631, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108631, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108632 q = 1) (hb : d149642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108632, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108632, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108633 q = 1) (hb : d149643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108633, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108633, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108634 q = 1) (hb : d149644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108634, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108634, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108636 q = 1) (hb : d149646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108636, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50291 q ha hb
    | true =>
      simp only [d108636, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108637 q = 1) (hb : d149647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108637, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108637, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108638 q = 1) (hb : d149648 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108638, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108638, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108639 q = 1) (hb : d149649 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108639, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108639, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108640 q = 1) (hb : d149650 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108640, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108640, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108641 q = 1) (hb : d149651 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108641, d149651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108641, d149651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50313 (p : Pattern) (ha : d108648 p = 1) (hb : d149658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108620 q = 1) (hb : d149630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108620, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50308 q ha hb
    | true =>
      simp only [d108620, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50290 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108550 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108621 q = 1) (hb : d149631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108621, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108623 q = 1) (hb : d149633 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108623, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50309 q ha hb
    | true =>
      simp only [d108623, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108624 q = 1) (hb : d149634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108624, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108624, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108625 q = 1) (hb : d149635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108625, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108646 q = 1) (hb : d149656 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108646, d149656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108646, d149656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108647 q = 1) (hb : d149657 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108647, d149657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108647, d149657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108648 q = 1) (hb : d149658 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108648, d149658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108648, d149658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50314 (p : Pattern) (ha : d108650 p = 1) (hb : d149660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108636 q = 1) (hb : d149646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108636, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50291 q ha hb
    | true =>
      simp only [d108636, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108637 q = 1) (hb : d149647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108637, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108637, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108638 q = 1) (hb : d149648 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108638, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108638, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108639 q = 1) (hb : d149649 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108639, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108639, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108640 q = 1) (hb : d149650 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108640, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108640, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108650 q = 1) (hb : d149660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108650, d149660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108650, d149660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50315 (p : Pattern) (ha : d53510 p = 1) (hb : d149666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53499 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17369 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
  have h3 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17370 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17371 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17372 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22930 q = 1) (hb : d53504 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22930, d53504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22930, d53504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53510 q = 1) (hb : d149666 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53510, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53510, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro50316 (p : Pattern) (ha : d53516 p = 1) (hb : d149670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17369 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
  have h2 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17370 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17371 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17372 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17376 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
  have h8 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17377 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17378 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17379 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22932 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22932, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22932, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53516 q = 1) (hb : d149670 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53516, d149670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d53516, d149670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50317 (p : Pattern) (ha : d53521 p = 1) (hb : d149675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17376 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
  have h2 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17377 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17378 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17379 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22943 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
  have h8 (q : Pattern) (ha : d22688 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
    | true =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22944 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22944, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22689 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22945 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22945, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22946 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22946, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22947 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22947, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22947, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53521 q = 1) (hb : d149675 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53521, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d53521, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50318 (p : Pattern) (ha : d108668 p = 1) (hb : d149681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108656 q = 1) (hb : d149667 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108656, d149667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50315 q ha hb
    | true =>
      simp only [d108656, d149667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108657 q = 1) (hb : d149668 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108657, d149668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108657, d149668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108658 q = 1) (hb : d149669 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108658, d149669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108658, d149669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108659 q = 1) (hb : d149671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108659, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50316 q ha hb
    | true =>
      simp only [d108659, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108660 q = 1) (hb : d149672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108660, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108660, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108661 q = 1) (hb : d149673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108661, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108661, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108662 q = 1) (hb : d149674 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108662, d149674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108662, d149674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108663 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108663, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50317 q ha hb
    | true =>
      simp only [d108663, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108664 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108664, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108664, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108665 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108665, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108665, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108666 q = 1) (hb : d149679 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108666, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108666, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108667 q = 1) (hb : d149680 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108667, d149680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108667, d149680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108668 q = 1) (hb : d149681 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108668, d149681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108668, d149681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50319 (p : Pattern) (ha : d108673 p = 1) (hb : d149686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108659 q = 1) (hb : d149671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108659, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50316 q ha hb
    | true =>
      simp only [d108659, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108660 q = 1) (hb : d149672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108660, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108660, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108661 q = 1) (hb : d149673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108661, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108661, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108663 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108663, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50317 q ha hb
    | true =>
      simp only [d108663, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108664 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108664, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108664, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108665 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108665, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108665, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108666 q = 1) (hb : d149679 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108666, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108666, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108671 q = 1) (hb : d149684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108671, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108671, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108672 q = 1) (hb : d149685 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108672, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108672, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108673 q = 1) (hb : d149686 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108673, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108673, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50320 (p : Pattern) (ha : d108679 p = 1) (hb : d149692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108669 q = 1) (hb : d149682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108669, d149682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50318 q ha hb
    | true =>
      simp only [d108669, d149682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108670 q = 1) (hb : d149683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108670, d149683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108670, d149683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108674 q = 1) (hb : d149687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108674, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50319 q ha hb
    | true =>
      simp only [d108674, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108675 q = 1) (hb : d149688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108675, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108675, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108676 q = 1) (hb : d149689 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108676, d149689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108676, d149689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108677 q = 1) (hb : d149690 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108677, d149690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108677, d149690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108678 q = 1) (hb : d149691 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108678, d149691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108678, d149691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108679 q = 1) (hb : d149692 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108679, d149692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108679, d149692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50321 (p : Pattern) (ha : d108681 p = 1) (hb : d149694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108663 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108663, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50317 q ha hb
    | true =>
      simp only [d108663, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108664 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108664, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108664, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108665 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108665, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108665, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108671 q = 1) (hb : d149684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108671, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108671, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108680 q = 1) (hb : d149693 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108680, d149693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108680, d149693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108681 q = 1) (hb : d149694 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108681, d149694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108681, d149694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50322 (p : Pattern) (ha : d108687 p = 1) (hb : d149700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108674 q = 1) (hb : d149687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108674, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50319 q ha hb
    | true =>
      simp only [d108674, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108675 q = 1) (hb : d149688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108675, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108675, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108682 q = 1) (hb : d149695 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108682, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50321 q ha hb
    | true =>
      simp only [d108682, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108683 q = 1) (hb : d149696 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108683, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108683, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108684 q = 1) (hb : d149697 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108684, d149697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108684, d149697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108685 q = 1) (hb : d149698 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108685, d149698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108685, d149698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108686 q = 1) (hb : d149699 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108686, d149699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108686, d149699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108687 q = 1) (hb : d149700 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108687, d149700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108687, d149700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50323 (p : Pattern) (ha : d74496 p = 1) (hb : d149675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17376 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
  have h2 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17377 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17378 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17379 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22943 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
  have h8 (q : Pattern) (ha : d22688 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
    | true =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22944 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22944, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22689 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22945 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22945, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22946 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22946, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22947 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22947, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22947, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74495 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74496 q = 1) (hb : d149675 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74496, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d74496, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50324 (p : Pattern) (ha : d108700 p = 1) (hb : d149686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108659 q = 1) (hb : d149671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108659, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50316 q ha hb
    | true =>
      simp only [d108659, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108660 q = 1) (hb : d149672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108660, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108660, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108661 q = 1) (hb : d149673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108661, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108661, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108663 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108663, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50317 q ha hb
    | true =>
      simp only [d108663, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108664 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108664, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108664, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108665 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108665, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108665, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108666 q = 1) (hb : d149679 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108666, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108666, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108695 q = 1) (hb : d149676 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108695, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50323 q ha hb
    | true =>
      simp only [d108695, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108696 q = 1) (hb : d149677 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108696, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108696, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108697 q = 1) (hb : d149678 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108697, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108697, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108698 q = 1) (hb : d149684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108698, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108698, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108699 q = 1) (hb : d149685 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108699, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108699, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108700 q = 1) (hb : d149686 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108700, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108700, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50325 (p : Pattern) (ha : d108706 p = 1) (hb : d149706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108701 q = 1) (hb : d149687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108701, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50324 q ha hb
    | true =>
      simp only [d108701, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108702 q = 1) (hb : d149688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108702, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108702, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108703 q = 1) (hb : d149703 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108703, d149703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108703, d149703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108704 q = 1) (hb : d149704 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108704, d149704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108704, d149704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108705 q = 1) (hb : d149705 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108705, d149705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108705, d149705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108706 q = 1) (hb : d149706 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108706, d149706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108706, d149706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50326 (p : Pattern) (ha : d108712 p = 1) (hb : d149712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108688 q = 1) (hb : d149701 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108688, d149701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50320 q ha hb
    | true =>
      simp only [d108688, d149701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50322 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108693 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108694 q = 1) (hb : d149702 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108694, d149702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108694, d149702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108707 q = 1) (hb : d149707 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108707, d149707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50325 q ha hb
    | true =>
      simp only [d108707, d149707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108708 q = 1) (hb : d149708 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108708, d149708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108708, d149708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108709 q = 1) (hb : d149709 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108709, d149709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108709, d149709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108710 q = 1) (hb : d149710 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108710, d149710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108710, d149710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108711 q = 1) (hb : d149711 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108711, d149711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108711, d149711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108712 q = 1) (hb : d149712 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108712, d149712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108712, d149712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50327 (p : Pattern) (ha : d108692 p = 1) (hb : d149717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108682 q = 1) (hb : d149695 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108682, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50321 q ha hb
    | true =>
      simp only [d108682, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108683 q = 1) (hb : d149696 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108683, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108683, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108689 q = 1) (hb : d149714 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108689, d149714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108689, d149714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108690 q = 1) (hb : d149715 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108690, d149715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108690, d149715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108691 q = 1) (hb : d149716 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108691, d149716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108691, d149716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108692 q = 1) (hb : d149717 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108692, d149717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108692, d149717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50328 (p : Pattern) (ha : d108719 p = 1) (hb : d149723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108714 q = 1) (hb : d149718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108714, d149718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50327 q ha hb
    | true =>
      simp only [d108714, d149718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108715 q = 1) (hb : d149719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108715, d149719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108715, d149719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108716 q = 1) (hb : d149720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108716, d149720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108716, d149720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108717 q = 1) (hb : d149721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108717, d149721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108717, d149721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108718 q = 1) (hb : d149722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108718, d149722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108718, d149722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108719 q = 1) (hb : d149723 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108719, d149723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108719, d149723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50329 (p : Pattern) (ha : d108725 p = 1) (hb : d149729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108546 q = 1) (hb : d149563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108546, d149563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108546, d149563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50289 q ha hb
  have h2 (q : Pattern) (ha : d108547 q = 1) (hb : d149564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108547, d149564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108547, d149564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108556 q = 1) (hb : d149573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108556, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50289 q ha hb
    | true =>
      simp only [d108556, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50292 q ha hb
  have h4 (q : Pattern) (ha : d108557 q = 1) (hb : d149574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108557, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108557, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108558 q = 1) (hb : d149575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108558, d149575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108558, d149575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108629 q = 1) (hb : d149639 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108629, d149639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50303 q ha hb
    | true =>
      simp only [d108629, d149639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50310 q ha hb
  have h7 (q : Pattern) (ha : d108642 q = 1) (hb : d149652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108642, d149652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50311 q ha hb
    | true =>
      simp only [d108642, d149652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50312 q ha hb
  have h8 (q : Pattern) (ha : d108643 q = 1) (hb : d149653 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108643, d149653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108643, d149653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108644 q = 1) (hb : d149654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108644, d149654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108644, d149654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d108645 q = 1) (hb : d149655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108645, d149655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108645, d149655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108649 q = 1) (hb : d149659 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108649, d149659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108649, d149659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50313 q ha hb
  have h12 (q : Pattern) (ha : d108651 q = 1) (hb : d149661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108651, d149661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108651, d149661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50314 q ha hb
  have h13 (q : Pattern) (ha : d108652 q = 1) (hb : d149662 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108652, d149662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108652, d149662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108653 q = 1) (hb : d149663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108653, d149663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108653, d149663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d108654 q = 1) (hb : d149664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108654, d149664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108654, d149664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d108655 q = 1) (hb : d149665 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108655, d149665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108655, d149665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108713 q = 1) (hb : d149713 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108713, d149713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108713, d149713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50326 q ha hb
  have h18 (q : Pattern) (ha : d108720 q = 1) (hb : d149724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108720, d149724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108720, d149724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50328 q ha hb
  have h19 (q : Pattern) (ha : d108721 q = 1) (hb : d149725 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108721, d149725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108721, d149725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108722 q = 1) (hb : d149726 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108722, d149726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108722, d149726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108723 q = 1) (hb : d149727 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108723, d149727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108723, d149727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108724 q = 1) (hb : d149728 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108724, d149728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108724, d149728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108725 q = 1) (hb : d149729 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108725, d149729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108725, d149729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro50330 (p : Pattern) (ha : d108731 p = 1) (hb : d149735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108726 q = 1) (hb : d149730 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108726, d149730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108726, d149730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50329 q ha hb
  have h2 (q : Pattern) (ha : d108727 q = 1) (hb : d149731 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108727, d149731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108727, d149731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108728 q = 1) (hb : d149732 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108728, d149732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108728, d149732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108729 q = 1) (hb : d149733 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108729, d149733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108729, d149733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108730 q = 1) (hb : d149734 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108730, d149734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108730, d149734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108731 q = 1) (hb : d149735 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108731, d149735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108731, d149735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50331 (p : Pattern) (ha : d108737 p = 1) (hb : d149741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d107858 q = 1) (hb : d148924 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d107858, d148924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50098 q ha hb
    | true =>
      simp only [d107858, d148924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50138 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108075 q = 1) (hb : d149112 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108075, d149112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108075, d149112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50186 q ha hb
  have h3 (q : Pattern) (ha : d108076 q = 1) (hb : d149113 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108076, d149113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108076, d149113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108293 q = 1) (hb : d149319 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108293, d149319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108293, d149319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50234 q ha hb
  have h5 (q : Pattern) (ha : d108294 q = 1) (hb : d149320 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108294, d149320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108294, d149320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108295 q = 1) (hb : d149321 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108295, d149321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108295, d149321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108512 q = 1) (hb : d149527 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108512, d149527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108512, d149527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50282 q ha hb
  have h8 (q : Pattern) (ha : d108513 q = 1) (hb : d149528 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108513, d149528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108513, d149528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108514 q = 1) (hb : d149529 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108514, d149529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108514, d149529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108515 q = 1) (hb : d149530 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108515, d149530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108515, d149530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108732 q = 1) (hb : d149736 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108732, d149736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108732, d149736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50330 q ha hb
  have h12 (q : Pattern) (ha : d108733 q = 1) (hb : d149737 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108733, d149737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108733, d149737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108734 q = 1) (hb : d149738 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108734, d149738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108734, d149738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108735 q = 1) (hb : d149739 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108735, d149739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108735, d149739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108736 q = 1) (hb : d149740 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d108736, d149740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108736, d149740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108737 q = 1) (hb : d149741 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d108737, d149741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108737, d149741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro50332 (p : Pattern) (ha : d108743 p = 1) (hb : d149747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108738 q = 1) (hb : d149742 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d108738, d149742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50331 q ha hb
    | true =>
      simp only [d108738, d149742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108739 q = 1) (hb : d149743 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d108739, d149743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108739, d149743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108740 q = 1) (hb : d149744 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d108740, d149744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108740, d149744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108741 q = 1) (hb : d149745 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d108741, d149745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108741, d149745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108742 q = 1) (hb : d149746 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d108742, d149746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108742, d149746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108743 q = 1) (hb : d149747 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d108743, d149747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108743, d149747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50333 (p : Pattern) (ha : d108749 p = 1) (hb : d149753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108744 q = 1) (hb : d149748 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d108744, d149748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50332 q ha hb
    | true =>
      simp only [d108744, d149748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108745 q = 1) (hb : d149749 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d108745, d149749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108745, d149749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108746 q = 1) (hb : d149750 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d108746, d149750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108746, d149750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108747 q = 1) (hb : d149751 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d108747, d149751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108747, d149751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108748 q = 1) (hb : d149752 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d108748, d149752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108748, d149752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108749 q = 1) (hb : d149753 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d108749, d149753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108749, d149753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50334 (p : Pattern) (ha : d108755 p = 1) (hb : d149759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108750 q = 1) (hb : d149754 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d108750, d149754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50333 q ha hb
    | true =>
      simp only [d108750, d149754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108751 q = 1) (hb : d149755 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d108751, d149755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108751, d149755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108752 q = 1) (hb : d149756 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d108752, d149756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108752, d149756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108753 q = 1) (hb : d149757 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d108753, d149757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108753, d149757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108754 q = 1) (hb : d149758 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d108754, d149758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108754, d149758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108755 q = 1) (hb : d149759 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d108755, d149759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108755, d149759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50335 (p : Pattern) (ha : d108761 p = 1) (hb : d149765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108756 q = 1) (hb : d149760 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d108756, d149760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50334 q ha hb
    | true =>
      simp only [d108756, d149760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108757 q = 1) (hb : d149761 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d108757, d149761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108757, d149761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108758 q = 1) (hb : d149762 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d108758, d149762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108758, d149762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108759 q = 1) (hb : d149763 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d108759, d149763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108759, d149763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108760 q = 1) (hb : d149764 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d108760, d149764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108760, d149764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108761 q = 1) (hb : d149765 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d108761, d149765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108761, d149765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50336 (p : Pattern) (ha : d108767 p = 1) (hb : d149771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108762 q = 1) (hb : d149766 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d108762, d149766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50335 q ha hb
    | true =>
      simp only [d108762, d149766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108763 q = 1) (hb : d149767 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d108763, d149767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108763, d149767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108764 q = 1) (hb : d149768 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d108764, d149768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108764, d149768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108765 q = 1) (hb : d149769 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d108765, d149769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108765, d149769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108766 q = 1) (hb : d149770 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d108766, d149770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108766, d149770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108767 q = 1) (hb : d149771 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d108767, d149771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108767, d149771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50337 (p : Pattern) (ha : d108773 p = 1) (hb : d149777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108768 q = 1) (hb : d149772 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d108768, d149772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50336 q ha hb
    | true =>
      simp only [d108768, d149772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108769 q = 1) (hb : d149773 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d108769, d149773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108769, d149773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108770 q = 1) (hb : d149774 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d108770, d149774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108770, d149774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108771 q = 1) (hb : d149775 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d108771, d149775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108771, d149775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108772 q = 1) (hb : d149776 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d108772, d149776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108772, d149776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108773 q = 1) (hb : d149777 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d108773, d149777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108773, d149777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50338 (p : Pattern) (ha : d108779 p = 1) (hb : d149783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108774 q = 1) (hb : d149778 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d108774, d149778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50337 q ha hb
    | true =>
      simp only [d108774, d149778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108775 q = 1) (hb : d149779 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d108775, d149779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108775, d149779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108776 q = 1) (hb : d149780 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d108776, d149780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108776, d149780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108777 q = 1) (hb : d149781 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d108777, d149781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108777, d149781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108778 q = 1) (hb : d149782 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d108778, d149782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108778, d149782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108779 q = 1) (hb : d149783 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d108779, d149783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108779, d149783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50339 (p : Pattern) (ha : d146837 p = 1) (hb : d194340 p = 1) : d149786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d146837 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20913 q = 1) (hb : d146837 q = 1) : d148567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49823 q ha hb
    | true =>
      simp only [d20913, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20969 q = 1) (hb : d146837 q = 1) : d148622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20970 q = 1) (hb : d146837 q = 1) : d148623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20970, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20971 q = 1) (hb : d146837 q = 1) : d148624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20972 q = 1) (hb : d146837 q = 1) : d148625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194340 q = 1) : d149786 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194340, d149786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194340, d149786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro50340 (p : Pattern) (ha : d146837 p = 1) (hb : d194350 p = 1) : d149796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d146837 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20945 q = 1) (hb : d146837 q = 1) : d148598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49827 q ha hb
    | true =>
      simp only [d20945, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194346 q = 1) : d149792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194346, d149792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194346, d149792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194347 q = 1) : d149793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194347, d149793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194347, d149793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194348 q = 1) : d149794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194348, d149794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194348, d149794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194349 q = 1) : d149795 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194349, d149795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194349, d149795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194350 q = 1) : d149796 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194350, d149796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194350, d149796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro50341 (p : Pattern) (ha : d146837 p = 1) (hb : d194356 p = 1) : d149802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20974 q = 1) (hb : d146837 q = 1) : d148627 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49830 q ha hb
    | true =>
      simp only [d20974, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49831 q ha hb
  have h2 (q : Pattern) (ha : d20975 q = 1) (hb : d146837 q = 1) : d148628 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20975, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194338 q = 1) : d149784 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194338, d149784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194338, d149784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194339 q = 1) : d149785 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194339, d149785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194339, d149785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194341 q = 1) : d149787 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194341, d149787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194341, d149787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50339 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194342 q = 1) : d149788 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194342, d149788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194342, d149788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194343 q = 1) : d149789 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194343, d149789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194343, d149789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d194344 q = 1) : d149790 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194344, d149790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194344, d149790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d194345 q = 1) : d149791 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194345, d149791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194345, d149791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d194351 q = 1) : d149797 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194351, d149797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194351, d149797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50340 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d194352 q = 1) : d149798 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194352, d149798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194352, d149798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d194353 q = 1) : d149799 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194353, d149799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194353, d149799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d194354 q = 1) : d149800 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194354, d149800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194354, d149800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d194355 q = 1) : d149801 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194355, d149801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194355, d149801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d194356 q = 1) : d149802 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194356, d149802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194356, d149802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro50342 (p : Pattern) (ha : d146837 p = 1) (hb : d194362 p = 1) : d149808 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d146837 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194357 q = 1) : d149803 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194357, d149803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194357, d149803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50341 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194358 q = 1) : d149804 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194358, d149804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194358, d149804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194359 q = 1) : d149805 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194359, d149805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194359, d149805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194360 q = 1) : d149806 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194360, d149806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194360, d149806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194361 q = 1) : d149807 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194361, d149807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194361, d149807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194362 q = 1) : d149808 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194362, d149808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194362, d149808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro50343 (p : Pattern) (ha : d146837 p = 1) (hb : d194365 p = 1) : d149811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21156 q = 1) (hb : d146837 q = 1) : d148764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49856 q ha hb
    | true =>
      simp only [d21156, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49857 q ha hb
  have h2 (q : Pattern) (ha : d21157 q = 1) (hb : d146837 q = 1) : d148765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21158 q = 1) (hb : d146837 q = 1) : d148766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21158, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21159 q = 1) (hb : d146837 q = 1) : d148767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21160 q = 1) (hb : d146837 q = 1) : d148768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194365 q = 1) : d149811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194365, d149811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194365, d149811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro50344 (p : Pattern) (ha : d146837 p = 1) (hb : d194376 p = 1) : d149822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194371 q = 1) : d149817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194371, d149817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49884 q hb ha
    | true =>
      simp only [d194371, d149817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49863 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194372 q = 1) : d149818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194372, d149818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194372, d149818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194373 q = 1) : d149819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194373, d149819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194373, d149819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194374 q = 1) : d149820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194374, d149820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194374, d149820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194375 q = 1) : d149821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194375, d149821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194375, d149821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194376 q = 1) : d149822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194376, d149822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194376, d149822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50345 (p : Pattern) (ha : d146837 p = 1) (hb : d194382 p = 1) : d149828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21162 q = 1) (hb : d146837 q = 1) : d148770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49855 q ha hb
    | true =>
      simp only [d21162, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49858 q ha hb
  have h2 (q : Pattern) (ha : d21163 q = 1) (hb : d146837 q = 1) : d148771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21163, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194363 q = 1) : d149809 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194363, d149809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194363, d149809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194364 q = 1) : d149810 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194364, d149810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194364, d149810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194366 q = 1) : d149812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194366, d149812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194366, d149812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50343 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194367 q = 1) : d149813 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194367, d149813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194367, d149813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194368 q = 1) : d149814 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194368, d149814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194368, d149814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d194369 q = 1) : d149815 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194369, d149815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194369, d149815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d194370 q = 1) : d149816 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194370, d149816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194370, d149816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d194377 q = 1) : d149823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194377, d149823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194377, d149823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50344 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d194378 q = 1) : d149824 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194378, d149824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194378, d149824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d194379 q = 1) : d149825 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194379, d149825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194379, d149825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d194380 q = 1) : d149826 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194380, d149826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194380, d149826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d194381 q = 1) : d149827 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194381, d149827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194381, d149827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d194382 q = 1) : d149828 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194382, d149828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194382, d149828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro50346 (p : Pattern) (ha : d146837 p = 1) (hb : d194388 p = 1) : d149834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194383 q = 1) : d149829 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194383, d149829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194383, d149829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50345 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194384 q = 1) : d149830 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194384, d149830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194384, d149830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194385 q = 1) : d149831 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194385, d149831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194385, d149831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194386 q = 1) : d149832 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194386, d149832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194386, d149832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194387 q = 1) : d149833 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194387, d149833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194387, d149833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194388 q = 1) : d149834 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194388, d149834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194388, d149834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50347 (p : Pattern) (ha : d146837 p = 1) (hb : d194392 p = 1) : d149838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21455 q = 1) (hb : d146837 q = 1) : d148952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49894 q ha hb
    | true =>
      simp only [d21455, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49895 q ha hb
  have h2 (q : Pattern) (ha : d21456 q = 1) (hb : d146837 q = 1) : d148953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21457 q = 1) (hb : d146837 q = 1) : d148954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21457, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21458 q = 1) (hb : d146837 q = 1) : d148955 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21459 q = 1) (hb : d146837 q = 1) : d148956 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194392 q = 1) : d149838 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194392, d149838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194392, d149838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro50348 (p : Pattern) (ha : d146837 p = 1) (hb : d194403 p = 1) : d149849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194398 q = 1) : d149844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194398, d149844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49922 q hb ha
    | true =>
      simp only [d194398, d149844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49901 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194399 q = 1) : d149845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194399, d149845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194399, d149845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194400 q = 1) : d149846 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194400, d149846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194400, d149846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194401 q = 1) : d149847 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194401, d149847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194401, d149847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194402 q = 1) : d149848 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194402, d149848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194402, d149848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194403 q = 1) : d149849 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194403, d149849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194403, d149849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50349 (p : Pattern) (ha : d146837 p = 1) (hb : d194409 p = 1) : d149855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21461 q = 1) (hb : d146837 q = 1) : d148958 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49893 q ha hb
    | true =>
      simp only [d21461, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49896 q ha hb
  have h2 (q : Pattern) (ha : d21462 q = 1) (hb : d146837 q = 1) : d148959 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21462, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194390 q = 1) : d149836 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194390, d149836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194390, d149836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194391 q = 1) : d149837 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194391, d149837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194391, d149837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194393 q = 1) : d149839 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194393, d149839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194393, d149839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50347 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194394 q = 1) : d149840 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194394, d149840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194394, d149840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194395 q = 1) : d149841 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194395, d149841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194395, d149841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d194396 q = 1) : d149842 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194396, d149842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194396, d149842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d194397 q = 1) : d149843 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194397, d149843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194397, d149843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d194404 q = 1) : d149850 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194404, d149850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194404, d149850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50348 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d194405 q = 1) : d149851 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194405, d149851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194405, d149851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d194406 q = 1) : d149852 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194406, d149852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194406, d149852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d194407 q = 1) : d149853 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194407, d149853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194407, d149853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d194408 q = 1) : d149854 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194408, d149854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194408, d149854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d194409 q = 1) : d149855 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194409, d149855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194409, d149855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro50350 (p : Pattern) (ha : d146837 p = 1) (hb : d194415 p = 1) : d149861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194410 q = 1) : d149856 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194410, d149856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194410, d149856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50349 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194411 q = 1) : d149857 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194411, d149857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194411, d149857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194412 q = 1) : d149858 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194412, d149858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194412, d149858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194413 q = 1) : d149859 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194413, d149859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194413, d149859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194414 q = 1) : d149860 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194414, d149860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194414, d149860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194415 q = 1) : d149861 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194415, d149861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194415, d149861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50351 (p : Pattern) (ha : d146837 p = 1) (hb : d194420 p = 1) : d149866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21808 q = 1) (hb : d146837 q = 1) : d149150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49932 q ha hb
    | true =>
      simp only [d21808, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49933 q ha hb
  have h2 (q : Pattern) (ha : d21809 q = 1) (hb : d146837 q = 1) : d149151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21810 q = 1) (hb : d146837 q = 1) : d149152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21810, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21811 q = 1) (hb : d146837 q = 1) : d149153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21812 q = 1) (hb : d146837 q = 1) : d149154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194420 q = 1) : d149866 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194420, d149866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194420, d149866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro50352 (p : Pattern) (ha : d146837 p = 1) (hb : d194427 p = 1) : d149269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22069 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22070 q = 1) (hb : d146837 q = 1) : d149254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45890 q ha hb
    | true =>
      simp only [d22070, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22071 q = 1) (hb : d146837 q = 1) : d149255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22072 q = 1) (hb : d146837 q = 1) : d149256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22078 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22079 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22079, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22080 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22081 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22082 q = 1) (hb : d146837 q = 1) : d149262 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22082, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22097 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22098 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22098, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22099 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22100 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22101 q = 1) (hb : d146837 q = 1) : d149267 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22101, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d194426 q = 1) : d149268 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194426, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d194426, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d194427 q = 1) : d149269 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194427, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d194427, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro50353 (p : Pattern) (ha : d146837 p = 1) (hb : d194433 p = 1) : d149283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194428 q = 1) : d149270 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194428, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50352 q ha hb
    | true =>
      simp only [d194428, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194429 q = 1) : d149271 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194429, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194429, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d146837 q = 1) : d149278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49940 q ha hb
    | true =>
      simp only [d22104, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d146837 q = 1) : d149279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194430 q = 1) : d149280 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194430, d149280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194430, d149280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194431 q = 1) : d149281 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194431, d149281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194431, d149281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194432 q = 1) : d149282 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194432, d149282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194432, d149282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d194433 q = 1) : d149283 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194433, d149283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194433, d149283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50354 (p : Pattern) (ha : d146837 p = 1) (hb : d194439 p = 1) : d149877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194434 q = 1) : d149872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194434, d149872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50353 q ha hb
    | true =>
      simp only [d194434, d149872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49941 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194435 q = 1) : d149873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194435, d149873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194435, d149873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194436 q = 1) : d149874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194436, d149874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194436, d149874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194437 q = 1) : d149875 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194437, d149875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194437, d149875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194438 q = 1) : d149876 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194438, d149876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194438, d149876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194439 q = 1) : d149877 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194439, d149877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194439, d149877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50355 (p : Pattern) (ha : d146837 p = 1) (hb : d194445 p = 1) : d149883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21814 q = 1) (hb : d146837 q = 1) : d149156 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49931 q ha hb
    | true =>
      simp only [d21814, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49934 q ha hb
  have h2 (q : Pattern) (ha : d21815 q = 1) (hb : d146837 q = 1) : d149157 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21815, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194418 q = 1) : d149864 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194418, d149864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194418, d149864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194419 q = 1) : d149865 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194419, d149865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194419, d149865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194421 q = 1) : d149867 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194421, d149867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194421, d149867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50351 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194422 q = 1) : d149868 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194422, d149868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194422, d149868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194423 q = 1) : d149869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194423, d149869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194423, d149869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d194424 q = 1) : d149870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194424, d149870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194424, d149870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d194425 q = 1) : d149871 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194425, d149871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194425, d149871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d194440 q = 1) : d149878 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194440, d149878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194440, d149878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50354 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d194441 q = 1) : d149879 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194441, d149879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194441, d149879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d194442 q = 1) : d149880 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194442, d149880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194442, d149880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d194443 q = 1) : d149881 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194443, d149881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194443, d149881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d194444 q = 1) : d149882 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194444, d149882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194444, d149882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d194445 q = 1) : d149883 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194445, d149883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194445, d149883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro50356 (p : Pattern) (ha : d146837 p = 1) (hb : d194451 p = 1) : d149889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194446 q = 1) : d149884 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194446, d149884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194446, d149884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50355 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194447 q = 1) : d149885 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194447, d149885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194447, d149885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194448 q = 1) : d149886 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194448, d149886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194448, d149886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194449 q = 1) : d149887 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194449, d149887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194449, d149887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194450 q = 1) : d149888 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194450, d149888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194450, d149888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194451 q = 1) : d149889 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194451, d149889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194451, d149889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50357 (p : Pattern) (ha : d146837 p = 1) (hb : d194457 p = 1) : d149895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22286 q = 1) (hb : d146837 q = 1) : d149358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49975 q ha hb
    | true =>
      simp only [d22286, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49976 q ha hb
  have h2 (q : Pattern) (ha : d22287 q = 1) (hb : d146837 q = 1) : d149359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22288 q = 1) (hb : d146837 q = 1) : d149360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22288, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22289 q = 1) (hb : d146837 q = 1) : d149361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22290 q = 1) (hb : d146837 q = 1) : d149362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194457 q = 1) : d149895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194457, d149895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194457, d149895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro50358 (p : Pattern) (ha : d146837 p = 1) (hb : d194464 p = 1) : d149477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22534 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22535 q = 1) (hb : d146837 q = 1) : d149462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d146837, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45945 q ha hb
    | true =>
      simp only [d22535, d146837, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22536 q = 1) (hb : d146837 q = 1) : d149463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22537 q = 1) (hb : d146837 q = 1) : d149464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22543 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22544 q = 1) (hb : d146837 q = 1) : d149467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
    | true =>
      simp only [d22544, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22545 q = 1) (hb : d146837 q = 1) : d149468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22546 q = 1) (hb : d146837 q = 1) : d149469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22547 q = 1) (hb : d146837 q = 1) : d149470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22547, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22562 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22563 q = 1) (hb : d146837 q = 1) : d149467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
    | true =>
      simp only [d22563, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22564 q = 1) (hb : d146837 q = 1) : d149468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22565 q = 1) (hb : d146837 q = 1) : d149469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22566 q = 1) (hb : d146837 q = 1) : d149475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22566, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d194463 q = 1) : d149476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194463, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d194463, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d194464 q = 1) : d149477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194464, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d194464, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro50359 (p : Pattern) (ha : d146837 p = 1) (hb : d194470 p = 1) : d149491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194465 q = 1) : d149478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194465, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50358 q ha hb
    | true =>
      simp only [d194465, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194466 q = 1) : d149479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194466, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194466, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22569 q = 1) (hb : d146837 q = 1) : d149486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49983 q ha hb
    | true =>
      simp only [d22569, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22570 q = 1) (hb : d146837 q = 1) : d149487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194467 q = 1) : d149488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194467, d149488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194467, d149488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194468 q = 1) : d149489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194468, d149489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194468, d149489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194469 q = 1) : d149490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194469, d149490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194469, d149490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d194470 q = 1) : d149491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194470, d149491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194470, d149491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50360 (p : Pattern) (ha : d146837 p = 1) (hb : d194476 p = 1) : d149906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194471 q = 1) : d149901 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194471, d149901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50359 q ha hb
    | true =>
      simp only [d194471, d149901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49984 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194472 q = 1) : d149902 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194472, d149902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194472, d149902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194473 q = 1) : d149903 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194473, d149903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194473, d149903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194474 q = 1) : d149904 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194474, d149904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194474, d149904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194475 q = 1) : d149905 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194475, d149905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194475, d149905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194476 q = 1) : d149906 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194476, d149906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194476, d149906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50361 (p : Pattern) (ha : d146837 p = 1) (hb : d194482 p = 1) : d149912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22292 q = 1) (hb : d146837 q = 1) : d149364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49974 q ha hb
    | true =>
      simp only [d22292, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49977 q ha hb
  have h2 (q : Pattern) (ha : d22293 q = 1) (hb : d146837 q = 1) : d149365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22293, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194455 q = 1) : d149893 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194455, d149893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194455, d149893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194456 q = 1) : d149894 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194456, d149894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194456, d149894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194458 q = 1) : d149896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194458, d149896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194458, d149896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50357 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194459 q = 1) : d149897 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194459, d149897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194459, d149897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194460 q = 1) : d149898 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194460, d149898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194460, d149898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d194461 q = 1) : d149899 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194461, d149899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194461, d149899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d194462 q = 1) : d149900 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194462, d149900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194462, d149900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d194477 q = 1) : d149907 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194477, d149907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194477, d149907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50360 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d194478 q = 1) : d149908 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194478, d149908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194478, d149908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d194479 q = 1) : d149909 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194479, d149909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194479, d149909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d194480 q = 1) : d149910 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194480, d149910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194480, d149910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d194481 q = 1) : d149911 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194481, d149911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194481, d149911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d194482 q = 1) : d149912 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194482, d149912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194482, d149912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro50362 (p : Pattern) (ha : d146837 p = 1) (hb : d194488 p = 1) : d149918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194483 q = 1) : d149913 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194483, d149913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194483, d149913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50361 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194484 q = 1) : d149914 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194484, d149914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194484, d149914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194485 q = 1) : d149915 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194485, d149915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194485, d149915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194486 q = 1) : d149916 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194486, d149916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194486, d149916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194487 q = 1) : d149917 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194487, d149917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194487, d149917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194488 q = 1) : d149918 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194488, d149918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194488, d149918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50363 (p : Pattern) (ha : d146837 p = 1) (hb : d194495 p = 1) : d149925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22741 q = 1) (hb : d146837 q = 1) : d149567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50018 q ha hb
    | true =>
      simp only [d22741, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50019 q ha hb
  have h2 (q : Pattern) (ha : d22742 q = 1) (hb : d146837 q = 1) : d149568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22743 q = 1) (hb : d146837 q = 1) : d149569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22743, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22744 q = 1) (hb : d146837 q = 1) : d149570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22745 q = 1) (hb : d146837 q = 1) : d149571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194495 q = 1) : d149925 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194495, d149925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194495, d149925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro50364 (p : Pattern) (ha : d146837 p = 1) (hb : d194502 p = 1) : d149686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22948 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22949 q = 1) (hb : d146837 q = 1) : d149671 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d146837, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46000 q ha hb
    | true =>
      simp only [d22949, d146837, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22950 q = 1) (hb : d146837 q = 1) : d149672 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22951 q = 1) (hb : d146837 q = 1) : d149673 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22957 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22958 q = 1) (hb : d146837 q = 1) : d149676 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d146837, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45974 q ha hb
    | true =>
      simp only [d22958, d146837, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22959 q = 1) (hb : d146837 q = 1) : d149677 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22960 q = 1) (hb : d146837 q = 1) : d149678 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22961 q = 1) (hb : d146837 q = 1) : d149679 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22961, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22976 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22977 q = 1) (hb : d146837 q = 1) : d149676 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d146837, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45974 q ha hb
    | true =>
      simp only [d22977, d146837, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22978 q = 1) (hb : d146837 q = 1) : d149677 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22979 q = 1) (hb : d146837 q = 1) : d149678 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22980 q = 1) (hb : d146837 q = 1) : d149684 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22980, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d194501 q = 1) : d149685 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194501, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d194501, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d194502 q = 1) : d149686 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194502, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d194502, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro50365 (p : Pattern) (ha : d146837 p = 1) (hb : d194508 p = 1) : d149700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194503 q = 1) : d149687 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194503, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50364 q ha hb
    | true =>
      simp only [d194503, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194504 q = 1) : d149688 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194504, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194504, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22983 q = 1) (hb : d146837 q = 1) : d149695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50026 q ha hb
    | true =>
      simp only [d22983, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22984 q = 1) (hb : d146837 q = 1) : d149696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194505 q = 1) : d149697 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194505, d149697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194505, d149697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194506 q = 1) : d149698 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194506, d149698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194506, d149698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194507 q = 1) : d149699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194507, d149699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194507, d149699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d194508 q = 1) : d149700 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194508, d149700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194508, d149700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50366 (p : Pattern) (ha : d146837 p = 1) (hb : d194514 p = 1) : d149936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194509 q = 1) : d149931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194509, d149931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50365 q ha hb
    | true =>
      simp only [d194509, d149931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50027 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194510 q = 1) : d149932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194510, d149932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194510, d149932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194511 q = 1) : d149933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194511, d149933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194511, d149933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194512 q = 1) : d149934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194512, d149934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194512, d149934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194513 q = 1) : d149935 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194513, d149935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194513, d149935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194514 q = 1) : d149936 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194514, d149936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194514, d149936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50367 (p : Pattern) (ha : d146837 p = 1) (hb : d194520 p = 1) : d149942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22747 q = 1) (hb : d146837 q = 1) : d149573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50017 q ha hb
    | true =>
      simp only [d22747, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50020 q ha hb
  have h2 (q : Pattern) (ha : d22748 q = 1) (hb : d146837 q = 1) : d149574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22748, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194493 q = 1) : d149923 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194493, d149923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194493, d149923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194494 q = 1) : d149924 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194494, d149924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194494, d149924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194496 q = 1) : d149926 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194496, d149926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194496, d149926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50363 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194497 q = 1) : d149927 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194497, d149927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194497, d149927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194498 q = 1) : d149928 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194498, d149928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194498, d149928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d194499 q = 1) : d149929 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194499, d149929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194499, d149929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d194500 q = 1) : d149930 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194500, d149930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194500, d149930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d194515 q = 1) : d149937 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194515, d149937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194515, d149937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50366 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d194516 q = 1) : d149938 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194516, d149938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194516, d149938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d194517 q = 1) : d149939 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194517, d149939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194517, d149939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d194518 q = 1) : d149940 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194518, d149940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194518, d149940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d194519 q = 1) : d149941 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194519, d149941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194519, d149941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d194520 q = 1) : d149942 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194520, d149942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194520, d149942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro50368 (p : Pattern) (ha : d146837 p = 1) (hb : d194526 p = 1) : d149948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194521 q = 1) : d149943 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194521, d149943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194521, d149943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50367 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194522 q = 1) : d149944 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194522, d149944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194522, d149944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194523 q = 1) : d149945 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194523, d149945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194523, d149945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194524 q = 1) : d149946 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194524, d149946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194524, d149946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194525 q = 1) : d149947 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194525, d149947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194525, d149947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194526 q = 1) : d149948 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194526, d149948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194526, d149948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50369 (p : Pattern) (ha : d146837 p = 1) (hb : d194532 p = 1) : d149954 p = 1 := by
  have h0 (q : Pattern) (ha : d146837 q = 1) (hb : d194389 q = 1) : d149835 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194389, d149835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50342 q ha hb
    | true =>
      simp only [d194389, d149835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50346 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194416 q = 1) : d149862 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194416, d149862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194416, d149862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50350 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194417 q = 1) : d149863 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194417, d149863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194417, d149863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194452 q = 1) : d149890 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194452, d149890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194452, d149890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50356 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194453 q = 1) : d149891 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194453, d149891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194453, d149891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194454 q = 1) : d149892 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194454, d149892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194454, d149892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d194489 q = 1) : d149919 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194489, d149919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194489, d149919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50362 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d194490 q = 1) : d149920 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194490, d149920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194490, d149920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d194491 q = 1) : d149921 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194491, d149921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194491, d149921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d194492 q = 1) : d149922 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194492, d149922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194492, d149922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d194527 q = 1) : d149949 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194527, d149949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194527, d149949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50368 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d194528 q = 1) : d149950 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194528, d149950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194528, d149950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d194529 q = 1) : d149951 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194529, d149951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194529, d149951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d194530 q = 1) : d149952 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194530, d149952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194530, d149952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d194531 q = 1) : d149953 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d194531, d149953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194531, d149953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d194532 q = 1) : d149954 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d194532, d149954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d194532, d149954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro50370 (p : Pattern) (ha : d146837 p = 1) (hb : d194538 p = 1) : d149960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194533 q = 1) : d149955 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d194533, d149955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50369 q ha hb
    | true =>
      simp only [d194533, d149955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194534 q = 1) : d149956 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d194534, d149956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194534, d149956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194535 q = 1) : d149957 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d194535, d149957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194535, d149957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194536 q = 1) : d149958 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d194536, d149958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194536, d149958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194537 q = 1) : d149959 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d194537, d149959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194537, d149959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194538 q = 1) : d149960 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d194538, d149960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194538, d149960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50371 (p : Pattern) (ha : d146837 p = 1) (hb : d194544 p = 1) : d149966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194539 q = 1) : d149961 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d194539, d149961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50370 q ha hb
    | true =>
      simp only [d194539, d149961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194540 q = 1) : d149962 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d194540, d149962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194540, d149962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194541 q = 1) : d149963 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d194541, d149963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194541, d149963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194542 q = 1) : d149964 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d194542, d149964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194542, d149964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194543 q = 1) : d149965 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d194543, d149965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194543, d149965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194544 q = 1) : d149966 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d194544, d149966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194544, d149966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50372 (p : Pattern) (ha : d146837 p = 1) (hb : d194550 p = 1) : d149972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194545 q = 1) : d149967 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d194545, d149967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50371 q ha hb
    | true =>
      simp only [d194545, d149967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194546 q = 1) : d149968 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d194546, d149968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194546, d149968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194547 q = 1) : d149969 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d194547, d149969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194547, d149969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194548 q = 1) : d149970 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d194548, d149970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194548, d149970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194549 q = 1) : d149971 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d194549, d149971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194549, d149971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194550 q = 1) : d149972 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d194550, d149972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194550, d149972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50373 (p : Pattern) (ha : d146837 p = 1) (hb : d194556 p = 1) : d149978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194551 q = 1) : d149973 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d194551, d149973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50372 q ha hb
    | true =>
      simp only [d194551, d149973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194552 q = 1) : d149974 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d194552, d149974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194552, d149974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194553 q = 1) : d149975 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d194553, d149975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194553, d149975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194554 q = 1) : d149976 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d194554, d149976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194554, d149976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194555 q = 1) : d149977 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d194555, d149977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194555, d149977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194556 q = 1) : d149978 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d194556, d149978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194556, d149978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50374 (p : Pattern) (ha : d146837 p = 1) (hb : d194562 p = 1) : d149984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194557 q = 1) : d149979 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d194557, d149979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50373 q ha hb
    | true =>
      simp only [d194557, d149979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194558 q = 1) : d149980 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d194558, d149980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194558, d149980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194559 q = 1) : d149981 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d194559, d149981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194559, d149981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194560 q = 1) : d149982 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d194560, d149982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194560, d149982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194561 q = 1) : d149983 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d194561, d149983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194561, d149983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194562 q = 1) : d149984 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d194562, d149984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194562, d149984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50375 (p : Pattern) (ha : d146837 p = 1) (hb : d194568 p = 1) : d149990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194563 q = 1) : d149985 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d194563, d149985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50374 q ha hb
    | true =>
      simp only [d194563, d149985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194564 q = 1) : d149986 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d194564, d149986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194564, d149986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194565 q = 1) : d149987 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d194565, d149987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194565, d149987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194566 q = 1) : d149988 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d194566, d149988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194566, d149988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194567 q = 1) : d149989 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d194567, d149989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194567, d149989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194568 q = 1) : d149990 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d194568, d149990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194568, d149990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50376 (p : Pattern) (ha : d146837 p = 1) (hb : d194574 p = 1) : d149996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d194569 q = 1) : d149991 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d194569, d149991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50375 q ha hb
    | true =>
      simp only [d194569, d149991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d194570 q = 1) : d149992 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d194570, d149992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194570, d149992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d194571 q = 1) : d149993 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d194571, d149993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194571, d149993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d194572 q = 1) : d149994 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d194572, d149994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194572, d149994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d194573 q = 1) : d149995 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d194573, d149995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194573, d149995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d194574 q = 1) : d149996 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d194574, d149996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194574, d149996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50377 (p : Pattern) (ha : d107602 p = 1) (hb : d148619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107591 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107498 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50066 q ha hb
    | true =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d107592 q = 1) (hb : d148615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107592, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107598 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107599 q = 1) (hb : d148616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107599, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107600 q = 1) (hb : d148617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107600, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107601 q = 1) (hb : d148618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107601, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107602 q = 1) (hb : d148619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107602, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107602, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50378 (p : Pattern) (ha : d107621 p = 1) (hb : d148626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107591 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107498 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50066 q ha hb
    | true =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d107592 q = 1) (hb : d148615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107592, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107598 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107599 q = 1) (hb : d148616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107599, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107600 q = 1) (hb : d148617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107600, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107601 q = 1) (hb : d148618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107601, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107607 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107611 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107613 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107505 q = 1) (hb : d148567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50068 q ha hb
    | true =>
      simp only [d107505, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d107614 q = 1) (hb : d148622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107614, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107617 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107618 q = 1) (hb : d148623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107618, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107619 q = 1) (hb : d148624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107619, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107619, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107620 q = 1) (hb : d148625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107620, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107620, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107621 q = 1) (hb : d148626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107621, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107621, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50379 (p : Pattern) (ha : d107630 p = 1) (hb : d149786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107613 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107505 q = 1) (hb : d148567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50068 q ha hb
    | true =>
      simp only [d107505, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d107614 q = 1) (hb : d148622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107614, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107617 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107618 q = 1) (hb : d148623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107618, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107628 q = 1) (hb : d148624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107628, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107628, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107629 q = 1) (hb : d148625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107629, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107629, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107630 q = 1) (hb : d149786 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107630, d149786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107630, d149786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50380 (p : Pattern) (ha : d107659 p = 1) (hb : d149796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107535 q = 1) (hb : d148598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107535, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50073 q ha hb
    | true =>
      simp only [d107535, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d107649 q = 1) (hb : d149792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107649, d149792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107649, d149792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107655 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107656 q = 1) (hb : d149793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107656, d149793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107656, d149793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107657 q = 1) (hb : d149794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107657, d149794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107657, d149794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107658 q = 1) (hb : d149795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107658, d149795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107658, d149795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107659 q = 1) (hb : d149796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107659, d149796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107659, d149796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50381 (p : Pattern) (ha : d107665 p = 1) (hb : d149802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107622 q = 1) (hb : d148627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107622, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50377 q ha hb
    | true =>
      simp only [d107622, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50378 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107624 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107625 q = 1) (hb : d148628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107625, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107625, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107626 q = 1) (hb : d149784 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107626, d149784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107626, d149784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107627 q = 1) (hb : d149785 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107627, d149785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107627, d149785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107631 q = 1) (hb : d149787 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107631, d149787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107631, d149787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50379 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107632 q = 1) (hb : d149788 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107632, d149788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107632, d149788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107633 q = 1) (hb : d149789 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107633, d149789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107633, d149789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107634 q = 1) (hb : d149790 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107634, d149790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107634, d149790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107635 q = 1) (hb : d149791 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107635, d149791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107635, d149791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107660 q = 1) (hb : d149797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107660, d149797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107660, d149797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50380 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107661 q = 1) (hb : d149798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107661, d149798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107661, d149798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107662 q = 1) (hb : d149799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107662, d149799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107662, d149799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d107663 q = 1) (hb : d149800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107663, d149800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107663, d149800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d107664 q = 1) (hb : d149801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107664, d149801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107664, d149801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d107665 q = 1) (hb : d149802 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107665, d149802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107665, d149802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50382 (p : Pattern) (ha : d107671 p = 1) (hb : d149808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d107547 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d107547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d107547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16176 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d107548 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d107548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d107548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d107549 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d107549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d107549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d107550 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d107550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d107550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d107551 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d107551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d107551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107666 q = 1) (hb : d149803 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107666, d149803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107666, d149803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50381 q ha hb
  have h8 (q : Pattern) (ha : d107667 q = 1) (hb : d149804 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107667, d149804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107667, d149804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107668 q = 1) (hb : d149805 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107668, d149805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107668, d149805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107669 q = 1) (hb : d149806 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107669, d149806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107669, d149806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107670 q = 1) (hb : d149807 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107670, d149807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107670, d149807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107671 q = 1) (hb : d149808 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107671, d149808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d107671, d149808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro50383 (p : Pattern) (ha : d107748 p = 1) (hb : d148759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107715 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107724 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107737 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107689 q = 1) (hb : d148754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50101 q ha hb
    | true =>
      simp only [d107689, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50102 q ha hb
  have h5 (q : Pattern) (ha : d107738 q = 1) (hb : d148755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107738, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107744 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107745 q = 1) (hb : d148756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107745, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107746 q = 1) (hb : d148757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107746, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107747 q = 1) (hb : d148758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107747, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107748 q = 1) (hb : d148759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107748, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107748, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50384 (p : Pattern) (ha : d107769 p = 1) (hb : d148769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107715 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107689 q = 1) (hb : d148754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50101 q ha hb
    | true =>
      simp only [d107689, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50102 q ha hb
  have h4 (q : Pattern) (ha : d107738 q = 1) (hb : d148755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107738, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107744 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107745 q = 1) (hb : d148756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107745, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107746 q = 1) (hb : d148757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107746, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107747 q = 1) (hb : d148758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107747, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107754 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107759 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107761 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107699 q = 1) (hb : d148764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107699, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50104 q ha hb
    | true =>
      simp only [d107699, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50105 q ha hb
  have h13 (q : Pattern) (ha : d107762 q = 1) (hb : d148765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107762, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107765 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107766 q = 1) (hb : d148766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107766, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107767 q = 1) (hb : d148767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107767, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107767, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107768 q = 1) (hb : d148768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107768, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107768, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107769 q = 1) (hb : d148769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107769, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107769, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50385 (p : Pattern) (ha : d107789 p = 1) (hb : d149811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107699 q = 1) (hb : d148764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107699, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50104 q ha hb
    | true =>
      simp only [d107699, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50105 q ha hb
  have h3 (q : Pattern) (ha : d107762 q = 1) (hb : d148765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107762, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107765 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107766 q = 1) (hb : d148766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107766, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107787 q = 1) (hb : d148767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107787, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107787, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107788 q = 1) (hb : d148768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107788, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107788, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107789 q = 1) (hb : d149811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107789, d149811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107789, d149811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50386 (p : Pattern) (ha : d107838 p = 1) (hb : d149822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107827 q = 1) (hb : d149817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107827, d149817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50132 q ha hb
    | true =>
      simp only [d107827, d149817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50135 q ha hb
  have h3 (q : Pattern) (ha : d107828 q = 1) (hb : d149818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107828, d149818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107828, d149818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107834 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107835 q = 1) (hb : d149819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107835, d149819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107835, d149819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107836 q = 1) (hb : d149820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107836, d149820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107836, d149820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107837 q = 1) (hb : d149821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107837, d149821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107837, d149821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107838 q = 1) (hb : d149822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107838, d149822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107838, d149822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50387 (p : Pattern) (ha : d107851 p = 1) (hb : d149828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107707 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107770 q = 1) (hb : d148770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107770, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50383 q ha hb
    | true =>
      simp only [d107770, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50384 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107783 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107784 q = 1) (hb : d148771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107784, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107784, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107785 q = 1) (hb : d149809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107785, d149809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107785, d149809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107786 q = 1) (hb : d149810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107786, d149810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107786, d149810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107790 q = 1) (hb : d149812 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107790, d149812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107790, d149812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50385 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107792 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107793 q = 1) (hb : d149813 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107793, d149813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107793, d149813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107794 q = 1) (hb : d149814 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107794, d149814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107794, d149814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107795 q = 1) (hb : d149815 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107795, d149815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107795, d149815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107796 q = 1) (hb : d149816 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107796, d149816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107796, d149816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107839 q = 1) (hb : d149823 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107839, d149823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107839, d149823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50386 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107846 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107847 q = 1) (hb : d149824 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107847, d149824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107847, d149824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107848 q = 1) (hb : d149825 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107848, d149825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107848, d149825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d107849 q = 1) (hb : d149826 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107849, d149826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107849, d149826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d107850 q = 1) (hb : d149827 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107850, d149827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107850, d149827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d107851 q = 1) (hb : d149828 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107851, d149828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107851, d149828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50388 (p : Pattern) (ha : d107857 p = 1) (hb : d149834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107852 q = 1) (hb : d149829 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107852, d149829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107852, d149829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50387 q ha hb
  have h2 (q : Pattern) (ha : d107853 q = 1) (hb : d149830 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107853, d149830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107853, d149830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107854 q = 1) (hb : d149831 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107854, d149831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107854, d149831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107855 q = 1) (hb : d149832 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107855, d149832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107855, d149832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107856 q = 1) (hb : d149833 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107856, d149833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107856, d149833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107857 q = 1) (hb : d149834 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107857, d149834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107857, d149834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50389 (p : Pattern) (ha : d107950 p = 1) (hb : d148947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107931 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107883 q = 1) (hb : d148942 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50143 q ha hb
    | true =>
      simp only [d107883, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50144 q ha hb
  have h5 (q : Pattern) (ha : d107932 q = 1) (hb : d148943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107932, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107946 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107947 q = 1) (hb : d148944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107947, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107948 q = 1) (hb : d148945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107948, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107949 q = 1) (hb : d148946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107949, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107950 q = 1) (hb : d148947 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107950, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107950, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50390 (p : Pattern) (ha : d107971 p = 1) (hb : d148957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107909 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107931 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107883 q = 1) (hb : d148942 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50143 q ha hb
    | true =>
      simp only [d107883, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50144 q ha hb
  have h4 (q : Pattern) (ha : d107932 q = 1) (hb : d148943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107932, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107946 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107947 q = 1) (hb : d148944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107947, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107948 q = 1) (hb : d148945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107948, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107949 q = 1) (hb : d148946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107949, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107956 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107961 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107963 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107893 q = 1) (hb : d148952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107893, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50146 q ha hb
    | true =>
      simp only [d107893, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50147 q ha hb
  have h13 (q : Pattern) (ha : d107964 q = 1) (hb : d148953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107964, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107967 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107968 q = 1) (hb : d148954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107968, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107969 q = 1) (hb : d148955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107969, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107969, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107970 q = 1) (hb : d148956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107970, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107970, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107971 q = 1) (hb : d148957 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107971, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107971, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50391 (p : Pattern) (ha : d107991 p = 1) (hb : d149838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107963 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107893 q = 1) (hb : d148952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107893, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50146 q ha hb
    | true =>
      simp only [d107893, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50147 q ha hb
  have h3 (q : Pattern) (ha : d107964 q = 1) (hb : d148953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107964, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107967 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107968 q = 1) (hb : d148954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107968, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107989 q = 1) (hb : d148955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107989, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107989, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107990 q = 1) (hb : d148956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107990, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107990, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107991 q = 1) (hb : d149838 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107991, d149838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107991, d149838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50392 (p : Pattern) (ha : d108055 p = 1) (hb : d149849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108036 q = 1) (hb : d149844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108036, d149844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50178 q ha hb
    | true =>
      simp only [d108036, d149844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50183 q ha hb
  have h3 (q : Pattern) (ha : d108037 q = 1) (hb : d149845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108037, d149845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108037, d149845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108051 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108052 q = 1) (hb : d149846 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108052, d149846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108052, d149846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108053 q = 1) (hb : d149847 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108053, d149847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108053, d149847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108054 q = 1) (hb : d149848 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108054, d149848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108054, d149848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108055 q = 1) (hb : d149849 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108055, d149849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108055, d149849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50393 (p : Pattern) (ha : d108068 p = 1) (hb : d149855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107972 q = 1) (hb : d148958 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107972, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50389 q ha hb
    | true =>
      simp only [d107972, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50390 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107986 q = 1) (hb : d148959 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107986, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107986, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107987 q = 1) (hb : d149836 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107987, d149836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107987, d149836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107988 q = 1) (hb : d149837 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107988, d149837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107988, d149837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107992 q = 1) (hb : d149839 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107992, d149839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107992, d149839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50391 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107994 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107995 q = 1) (hb : d149840 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107995, d149840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107995, d149840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107996 q = 1) (hb : d149841 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107996, d149841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107996, d149841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107997 q = 1) (hb : d149842 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107997, d149842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107997, d149842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107998 q = 1) (hb : d149843 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107998, d149843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107998, d149843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108056 q = 1) (hb : d149850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108056, d149850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108056, d149850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50392 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108063 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108064 q = 1) (hb : d149851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108064, d149851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108064, d149851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108065 q = 1) (hb : d149852 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108065, d149852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108065, d149852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108066 q = 1) (hb : d149853 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108066, d149853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108066, d149853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108067 q = 1) (hb : d149854 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108067, d149854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108067, d149854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108068 q = 1) (hb : d149855 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108068, d149855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108068, d149855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50394 (p : Pattern) (ha : d108074 p = 1) (hb : d149861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108069 q = 1) (hb : d149856 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108069, d149856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108069, d149856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50393 q ha hb
  have h2 (q : Pattern) (ha : d108070 q = 1) (hb : d149857 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108070, d149857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108070, d149857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108071 q = 1) (hb : d149858 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108071, d149858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108071, d149858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108072 q = 1) (hb : d149859 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108072, d149859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108072, d149859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108073 q = 1) (hb : d149860 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108073, d149860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108073, d149860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108074 q = 1) (hb : d149861 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108074, d149861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108074, d149861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50395 (p : Pattern) (ha : d108168 p = 1) (hb : d149145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108149 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108101 q = 1) (hb : d149140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50191 q ha hb
    | true =>
      simp only [d108101, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50192 q ha hb
  have h5 (q : Pattern) (ha : d108150 q = 1) (hb : d149141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108150, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108164 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108165 q = 1) (hb : d149142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108165, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108166 q = 1) (hb : d149143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108166, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108167 q = 1) (hb : d149144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108167, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108168 q = 1) (hb : d149145 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108168, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108168, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50396 (p : Pattern) (ha : d108189 p = 1) (hb : d149155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108136 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108101 q = 1) (hb : d149140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50191 q ha hb
    | true =>
      simp only [d108101, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50192 q ha hb
  have h4 (q : Pattern) (ha : d108150 q = 1) (hb : d149141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108150, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108164 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108165 q = 1) (hb : d149142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108165, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108166 q = 1) (hb : d149143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108166, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108167 q = 1) (hb : d149144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108167, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108174 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108179 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108181 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108111 q = 1) (hb : d149150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108111, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50194 q ha hb
    | true =>
      simp only [d108111, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50195 q ha hb
  have h13 (q : Pattern) (ha : d108182 q = 1) (hb : d149151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108182, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108185 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108186 q = 1) (hb : d149152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108186, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108187 q = 1) (hb : d149153 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108187, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108187, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108188 q = 1) (hb : d149154 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108188, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108188, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108189 q = 1) (hb : d149155 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108189, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108189, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50397 (p : Pattern) (ha : d108209 p = 1) (hb : d149866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108111 q = 1) (hb : d149150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108111, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50194 q ha hb
    | true =>
      simp only [d108111, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50195 q ha hb
  have h3 (q : Pattern) (ha : d108182 q = 1) (hb : d149151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108182, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108185 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108186 q = 1) (hb : d149152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108186, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108207 q = 1) (hb : d149153 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108207, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108207, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108208 q = 1) (hb : d149154 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108208, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108208, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108209 q = 1) (hb : d149866 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108209, d149866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108209, d149866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50398 (p : Pattern) (ha : d108273 p = 1) (hb : d149877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108249 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108254 q = 1) (hb : d149872 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108254, d149872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50226 q ha hb
    | true =>
      simp only [d108254, d149872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50231 q ha hb
  have h3 (q : Pattern) (ha : d108255 q = 1) (hb : d149873 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108255, d149873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108255, d149873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108269 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108270 q = 1) (hb : d149874 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108270, d149874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108270, d149874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108271 q = 1) (hb : d149875 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108271, d149875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108271, d149875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108272 q = 1) (hb : d149876 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108272, d149876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108272, d149876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108273 q = 1) (hb : d149877 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108273, d149877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108273, d149877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50399 (p : Pattern) (ha : d108286 p = 1) (hb : d149883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108119 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108190 q = 1) (hb : d149156 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108190, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50395 q ha hb
    | true =>
      simp only [d108190, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50396 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108203 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108204 q = 1) (hb : d149157 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108204, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108204, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108205 q = 1) (hb : d149864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108205, d149864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108205, d149864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108206 q = 1) (hb : d149865 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108206, d149865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108206, d149865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108210 q = 1) (hb : d149867 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108210, d149867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108210, d149867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50397 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108212 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108213 q = 1) (hb : d149868 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108213, d149868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108213, d149868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108214 q = 1) (hb : d149869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108214, d149869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108214, d149869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108215 q = 1) (hb : d149870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108215, d149870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108215, d149870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108216 q = 1) (hb : d149871 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108216, d149871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108216, d149871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108274 q = 1) (hb : d149878 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108274, d149878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108274, d149878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50398 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108281 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108282 q = 1) (hb : d149879 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108282, d149879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108282, d149879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108283 q = 1) (hb : d149880 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108283, d149880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108283, d149880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108284 q = 1) (hb : d149881 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108284, d149881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108284, d149881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108285 q = 1) (hb : d149882 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108285, d149882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108285, d149882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108286 q = 1) (hb : d149883 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108286, d149883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108286, d149883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50400 (p : Pattern) (ha : d108292 p = 1) (hb : d149889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108287 q = 1) (hb : d149884 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108287, d149884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108287, d149884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50399 q ha hb
  have h2 (q : Pattern) (ha : d108288 q = 1) (hb : d149885 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108288, d149885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108288, d149885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108289 q = 1) (hb : d149886 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108289, d149886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108289, d149886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108290 q = 1) (hb : d149887 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108290, d149887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108290, d149887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108291 q = 1) (hb : d149888 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108291, d149888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108291, d149888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108292 q = 1) (hb : d149889 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108292, d149889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108292, d149889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50401 (p : Pattern) (ha : d108387 p = 1) (hb : d149353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108346 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108355 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108368 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108320 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50239 q ha hb
    | true =>
      simp only [d108320, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50240 q ha hb
  have h5 (q : Pattern) (ha : d108369 q = 1) (hb : d149349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108369, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108383 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108384 q = 1) (hb : d149350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108384, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108385 q = 1) (hb : d149351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108385, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108386 q = 1) (hb : d149352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108386, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108387 q = 1) (hb : d149353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108387, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108387, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50402 (p : Pattern) (ha : d108408 p = 1) (hb : d149363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108346 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108368 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108320 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50239 q ha hb
    | true =>
      simp only [d108320, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50240 q ha hb
  have h4 (q : Pattern) (ha : d108369 q = 1) (hb : d149349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108369, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108383 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108384 q = 1) (hb : d149350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108384, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108385 q = 1) (hb : d149351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108385, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108386 q = 1) (hb : d149352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108386, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108393 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108398 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108400 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108330 q = 1) (hb : d149358 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108330, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50242 q ha hb
    | true =>
      simp only [d108330, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50243 q ha hb
  have h13 (q : Pattern) (ha : d108401 q = 1) (hb : d149359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108401, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108404 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108405 q = 1) (hb : d149360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108405, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108406 q = 1) (hb : d149361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108406, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108406, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108407 q = 1) (hb : d149362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108407, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108407, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108408 q = 1) (hb : d149363 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108408, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108408, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50403 (p : Pattern) (ha : d108428 p = 1) (hb : d149895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108330 q = 1) (hb : d149358 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108330, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50242 q ha hb
    | true =>
      simp only [d108330, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50243 q ha hb
  have h3 (q : Pattern) (ha : d108401 q = 1) (hb : d149359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108401, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108404 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108405 q = 1) (hb : d149360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108405, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108426 q = 1) (hb : d149361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108426, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108426, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108427 q = 1) (hb : d149362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108427, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108427, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108428 q = 1) (hb : d149895 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108428, d149895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108428, d149895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50404 (p : Pattern) (ha : d108492 p = 1) (hb : d149906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108473 q = 1) (hb : d149901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108473, d149901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50274 q ha hb
    | true =>
      simp only [d108473, d149901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50279 q ha hb
  have h3 (q : Pattern) (ha : d108474 q = 1) (hb : d149902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108474, d149902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108474, d149902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108488 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108489 q = 1) (hb : d149903 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108489, d149903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108489, d149903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108490 q = 1) (hb : d149904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108490, d149904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108490, d149904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108491 q = 1) (hb : d149905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108491, d149905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108491, d149905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108492 q = 1) (hb : d149906 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108492, d149906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108492, d149906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50405 (p : Pattern) (ha : d108505 p = 1) (hb : d149912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108338 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108409 q = 1) (hb : d149364 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108409, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50401 q ha hb
    | true =>
      simp only [d108409, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50402 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108423 q = 1) (hb : d149365 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108423, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108423, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108424 q = 1) (hb : d149893 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108424, d149893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108424, d149893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108425 q = 1) (hb : d149894 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108425, d149894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108425, d149894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108429 q = 1) (hb : d149896 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108429, d149896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108429, d149896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50403 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108431 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108432 q = 1) (hb : d149897 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108432, d149897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108432, d149897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108433 q = 1) (hb : d149898 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108433, d149898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108433, d149898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108434 q = 1) (hb : d149899 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108434, d149899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108434, d149899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108435 q = 1) (hb : d149900 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108435, d149900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108435, d149900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108493 q = 1) (hb : d149907 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108493, d149907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108493, d149907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50404 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108500 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108501 q = 1) (hb : d149908 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108501, d149908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108501, d149908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108502 q = 1) (hb : d149909 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108502, d149909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108502, d149909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108503 q = 1) (hb : d149910 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108503, d149910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108503, d149910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108504 q = 1) (hb : d149911 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108504, d149911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108504, d149911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108505 q = 1) (hb : d149912 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108505, d149912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108505, d149912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50406 (p : Pattern) (ha : d108511 p = 1) (hb : d149918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108506 q = 1) (hb : d149913 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108506, d149913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108506, d149913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50405 q ha hb
  have h2 (q : Pattern) (ha : d108507 q = 1) (hb : d149914 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108507, d149914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108507, d149914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108508 q = 1) (hb : d149915 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108508, d149915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108508, d149915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108509 q = 1) (hb : d149916 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108509, d149916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108509, d149916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108510 q = 1) (hb : d149917 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108510, d149917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108510, d149917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108511 q = 1) (hb : d149918 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108511, d149918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108511, d149918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50407 (p : Pattern) (ha : d108607 p = 1) (hb : d149562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108588 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108540 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50287 q ha hb
    | true =>
      simp only [d108540, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50288 q ha hb
  have h5 (q : Pattern) (ha : d108589 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108589, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108603 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108604 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108604, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108605 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108605, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108606 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108606, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108607 q = 1) (hb : d149562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108607, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108607, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50408 (p : Pattern) (ha : d108628 p = 1) (hb : d149572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108588 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108540 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50287 q ha hb
    | true =>
      simp only [d108540, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50288 q ha hb
  have h4 (q : Pattern) (ha : d108589 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108589, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108603 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108604 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108604, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108605 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108605, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108606 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108606, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108613 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108618 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108620 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108550 q = 1) (hb : d149567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108550, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50290 q ha hb
    | true =>
      simp only [d108550, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50291 q ha hb
  have h13 (q : Pattern) (ha : d108621 q = 1) (hb : d149568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108621, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108625 q = 1) (hb : d149569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108625, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108626 q = 1) (hb : d149570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108626, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108626, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108627 q = 1) (hb : d149571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108627, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108627, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108628 q = 1) (hb : d149572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108628, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108628, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50409 (p : Pattern) (ha : d108648 p = 1) (hb : d149925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108550 q = 1) (hb : d149567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108550, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50290 q ha hb
    | true =>
      simp only [d108550, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50291 q ha hb
  have h3 (q : Pattern) (ha : d108621 q = 1) (hb : d149568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108621, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108625 q = 1) (hb : d149569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108625, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108646 q = 1) (hb : d149570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108646, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108646, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108647 q = 1) (hb : d149571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108647, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108647, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108648 q = 1) (hb : d149925 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108648, d149925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108648, d149925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50410 (p : Pattern) (ha : d108712 p = 1) (hb : d149936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108693 q = 1) (hb : d149931 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108693, d149931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50322 q ha hb
    | true =>
      simp only [d108693, d149931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50327 q ha hb
  have h3 (q : Pattern) (ha : d108694 q = 1) (hb : d149932 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108694, d149932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108694, d149932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108708 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108709 q = 1) (hb : d149933 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108709, d149933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108709, d149933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108710 q = 1) (hb : d149934 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108710, d149934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108710, d149934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108711 q = 1) (hb : d149935 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108711, d149935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108711, d149935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108712 q = 1) (hb : d149936 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108712, d149936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108712, d149936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50411 (p : Pattern) (ha : d108725 p = 1) (hb : d149942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108558 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108629 q = 1) (hb : d149573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108629, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50407 q ha hb
    | true =>
      simp only [d108629, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50408 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108643 q = 1) (hb : d149574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108643, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108643, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108644 q = 1) (hb : d149923 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108644, d149923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108644, d149923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108645 q = 1) (hb : d149924 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108645, d149924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108645, d149924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108649 q = 1) (hb : d149926 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108649, d149926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108649, d149926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50409 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108651 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108652 q = 1) (hb : d149927 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108652, d149927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108652, d149927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108653 q = 1) (hb : d149928 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108653, d149928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108653, d149928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108654 q = 1) (hb : d149929 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108654, d149929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108654, d149929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108655 q = 1) (hb : d149930 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108655, d149930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108655, d149930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108713 q = 1) (hb : d149937 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108713, d149937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108713, d149937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50410 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108720 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108721 q = 1) (hb : d149938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108721, d149938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108721, d149938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108722 q = 1) (hb : d149939 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108722, d149939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108722, d149939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108723 q = 1) (hb : d149940 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108723, d149940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108723, d149940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108724 q = 1) (hb : d149941 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108724, d149941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108724, d149941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108725 q = 1) (hb : d149942 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108725, d149942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108725, d149942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50412 (p : Pattern) (ha : d108731 p = 1) (hb : d149948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108726 q = 1) (hb : d149943 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108726, d149943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108726, d149943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50411 q ha hb
  have h2 (q : Pattern) (ha : d108727 q = 1) (hb : d149944 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108727, d149944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108727, d149944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108728 q = 1) (hb : d149945 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108728, d149945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108728, d149945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108729 q = 1) (hb : d149946 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108729, d149946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108729, d149946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108730 q = 1) (hb : d149947 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108730, d149947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108730, d149947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108731 q = 1) (hb : d149948 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108731, d149948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108731, d149948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50413 (p : Pattern) (ha : d108737 p = 1) (hb : d149954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d107858 q = 1) (hb : d149835 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d107858, d149835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50382 q ha hb
    | true =>
      simp only [d107858, d149835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50388 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108075 q = 1) (hb : d149862 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108075, d149862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108075, d149862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50394 q ha hb
  have h3 (q : Pattern) (ha : d108076 q = 1) (hb : d149863 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108076, d149863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108076, d149863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108293 q = 1) (hb : d149890 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108293, d149890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108293, d149890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50400 q ha hb
  have h5 (q : Pattern) (ha : d108294 q = 1) (hb : d149891 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108294, d149891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108294, d149891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108295 q = 1) (hb : d149892 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108295, d149892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108295, d149892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108512 q = 1) (hb : d149919 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108512, d149919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108512, d149919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50406 q ha hb
  have h8 (q : Pattern) (ha : d108513 q = 1) (hb : d149920 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108513, d149920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108513, d149920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108514 q = 1) (hb : d149921 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108514, d149921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108514, d149921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108515 q = 1) (hb : d149922 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108515, d149922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108515, d149922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108732 q = 1) (hb : d149949 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108732, d149949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108732, d149949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50412 q ha hb
  have h12 (q : Pattern) (ha : d108733 q = 1) (hb : d149950 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108733, d149950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108733, d149950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108734 q = 1) (hb : d149951 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108734, d149951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108734, d149951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108735 q = 1) (hb : d149952 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108735, d149952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108735, d149952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108736 q = 1) (hb : d149953 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d108736, d149953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108736, d149953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108737 q = 1) (hb : d149954 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d108737, d149954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108737, d149954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro50414 (p : Pattern) (ha : d108743 p = 1) (hb : d149960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108738 q = 1) (hb : d149955 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d108738, d149955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50413 q ha hb
    | true =>
      simp only [d108738, d149955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108739 q = 1) (hb : d149956 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d108739, d149956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108739, d149956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108740 q = 1) (hb : d149957 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d108740, d149957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108740, d149957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108741 q = 1) (hb : d149958 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d108741, d149958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108741, d149958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108742 q = 1) (hb : d149959 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d108742, d149959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108742, d149959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108743 q = 1) (hb : d149960 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d108743, d149960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108743, d149960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50415 (p : Pattern) (ha : d108749 p = 1) (hb : d149966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108744 q = 1) (hb : d149961 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d108744, d149961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50414 q ha hb
    | true =>
      simp only [d108744, d149961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108745 q = 1) (hb : d149962 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d108745, d149962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108745, d149962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108746 q = 1) (hb : d149963 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d108746, d149963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108746, d149963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108747 q = 1) (hb : d149964 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d108747, d149964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108747, d149964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108748 q = 1) (hb : d149965 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d108748, d149965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108748, d149965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108749 q = 1) (hb : d149966 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d108749, d149966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108749, d149966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50416 (p : Pattern) (ha : d108755 p = 1) (hb : d149972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108750 q = 1) (hb : d149967 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d108750, d149967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50415 q ha hb
    | true =>
      simp only [d108750, d149967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108751 q = 1) (hb : d149968 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d108751, d149968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108751, d149968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108752 q = 1) (hb : d149969 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d108752, d149969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108752, d149969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108753 q = 1) (hb : d149970 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d108753, d149970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108753, d149970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108754 q = 1) (hb : d149971 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d108754, d149971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108754, d149971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108755 q = 1) (hb : d149972 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d108755, d149972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108755, d149972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50417 (p : Pattern) (ha : d108761 p = 1) (hb : d149978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108756 q = 1) (hb : d149973 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d108756, d149973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50416 q ha hb
    | true =>
      simp only [d108756, d149973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108757 q = 1) (hb : d149974 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d108757, d149974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108757, d149974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108758 q = 1) (hb : d149975 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d108758, d149975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108758, d149975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108759 q = 1) (hb : d149976 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d108759, d149976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108759, d149976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108760 q = 1) (hb : d149977 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d108760, d149977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108760, d149977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108761 q = 1) (hb : d149978 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d108761, d149978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108761, d149978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50418 (p : Pattern) (ha : d108767 p = 1) (hb : d149984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108762 q = 1) (hb : d149979 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d108762, d149979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50417 q ha hb
    | true =>
      simp only [d108762, d149979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108763 q = 1) (hb : d149980 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d108763, d149980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108763, d149980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108764 q = 1) (hb : d149981 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d108764, d149981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108764, d149981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108765 q = 1) (hb : d149982 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d108765, d149982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108765, d149982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108766 q = 1) (hb : d149983 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d108766, d149983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108766, d149983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108767 q = 1) (hb : d149984 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d108767, d149984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108767, d149984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50419 (p : Pattern) (ha : d108773 p = 1) (hb : d149990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108768 q = 1) (hb : d149985 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d108768, d149985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50418 q ha hb
    | true =>
      simp only [d108768, d149985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108769 q = 1) (hb : d149986 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d108769, d149986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108769, d149986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108770 q = 1) (hb : d149987 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d108770, d149987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108770, d149987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108771 q = 1) (hb : d149988 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d108771, d149988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108771, d149988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108772 q = 1) (hb : d149989 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d108772, d149989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108772, d149989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108773 q = 1) (hb : d149990 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d108773, d149990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108773, d149990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50420 (p : Pattern) (ha : d108779 p = 1) (hb : d149996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108774 q = 1) (hb : d149991 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d108774, d149991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50419 q ha hb
    | true =>
      simp only [d108774, d149991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108775 q = 1) (hb : d149992 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d108775, d149992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108775, d149992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108776 q = 1) (hb : d149993 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d108776, d149993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108776, d149993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108777 q = 1) (hb : d149994 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d108777, d149994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108777, d149994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108778 q = 1) (hb : d149995 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d108778, d149995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108778, d149995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108779 q = 1) (hb : d149996 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d108779, d149996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108779, d149996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50421 (p : Pattern) (ha : d108822 p = 1) (hb : d148619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108818 q = 1) (hb : d148615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108818, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10774 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108819 q = 1) (hb : d148616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108819, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108820 q = 1) (hb : d148617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108820, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108821 q = 1) (hb : d148618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108821, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108822 q = 1) (hb : d148619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108822, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108822, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50422 (p : Pattern) (ha : d108827 p = 1) (hb : d148626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108818 q = 1) (hb : d148615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108818, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10774 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108819 q = 1) (hb : d148616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108819, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108820 q = 1) (hb : d148617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108820, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108821 q = 1) (hb : d148618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108821, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10783 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10787 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10789 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d148567 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108823 q = 1) (hb : d148622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108823, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10795 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108824 q = 1) (hb : d148623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108824, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108825 q = 1) (hb : d148624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108825, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108825, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108826 q = 1) (hb : d148625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108826, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108826, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108827 q = 1) (hb : d148626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108827, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108827, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50423 (p : Pattern) (ha : d108834 p = 1) (hb : d149786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10789 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148567 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108823 q = 1) (hb : d148622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108823, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10795 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108824 q = 1) (hb : d148623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108824, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108832 q = 1) (hb : d148624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108832, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108832, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108833 q = 1) (hb : d148625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108833, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108833, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108834 q = 1) (hb : d149786 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108834, d149786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108834, d149786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50424 (p : Pattern) (ha : d108844 p = 1) (hb : d149796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108840 q = 1) (hb : d149792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108840, d149792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108840, d149792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10846 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108841 q = 1) (hb : d149793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108841, d149793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108841, d149793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108842 q = 1) (hb : d149794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108842, d149794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108842, d149794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108843 q = 1) (hb : d149795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108843, d149795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108843, d149795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108844 q = 1) (hb : d149796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108844, d149796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108844, d149796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50425 (p : Pattern) (ha : d108850 p = 1) (hb : d149802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10729 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108828 q = 1) (hb : d148627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108828, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50421 q ha hb
    | true =>
      simp only [d108828, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50422 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10802 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108829 q = 1) (hb : d148628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108829, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108829, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108830 q = 1) (hb : d149784 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108830, d149784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108830, d149784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108831 q = 1) (hb : d149785 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108831, d149785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108831, d149785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108835 q = 1) (hb : d149787 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108835, d149787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108835, d149787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50423 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108836 q = 1) (hb : d149788 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108836, d149788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108836, d149788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108837 q = 1) (hb : d149789 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108837, d149789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108837, d149789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108838 q = 1) (hb : d149790 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108838, d149790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108838, d149790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108839 q = 1) (hb : d149791 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108839, d149791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108839, d149791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108845 q = 1) (hb : d149797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108845, d149797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108845, d149797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50424 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108846 q = 1) (hb : d149798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108846, d149798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108846, d149798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108847 q = 1) (hb : d149799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108847, d149799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108847, d149799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108848 q = 1) (hb : d149800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108848, d149800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108848, d149800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108849 q = 1) (hb : d149801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108849, d149801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108849, d149801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108850 q = 1) (hb : d149802 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108850, d149802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108850, d149802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50426 (p : Pattern) (ha : d108856 p = 1) (hb : d149808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d108813 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16225 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d108814 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d108815 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d108816 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d108817 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108851 q = 1) (hb : d149803 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108851, d149803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108851, d149803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50425 q ha hb
  have h8 (q : Pattern) (ha : d108852 q = 1) (hb : d149804 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108852, d149804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108852, d149804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108853 q = 1) (hb : d149805 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108853, d149805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108853, d149805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108854 q = 1) (hb : d149806 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108854, d149806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108854, d149806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108855 q = 1) (hb : d149807 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108855, d149807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108855, d149807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108856 q = 1) (hb : d149808 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108856, d149808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d108856, d149808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro50427 (p : Pattern) (ha : d108861 p = 1) (hb : d148759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10906 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10915 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10928 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148754 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108857 q = 1) (hb : d148755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108857, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10957 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108858 q = 1) (hb : d148756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108858, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108859 q = 1) (hb : d148757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108859, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108860 q = 1) (hb : d148758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108860, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108861 q = 1) (hb : d148759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108861, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108861, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50428 (p : Pattern) (ha : d108866 p = 1) (hb : d148769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10906 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10915 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10928 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d148754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108857 q = 1) (hb : d148755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108857, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10957 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108858 q = 1) (hb : d148756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108858, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108859 q = 1) (hb : d148757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108859, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108860 q = 1) (hb : d148758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108860, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10967 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10972 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10974 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d148764 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108862 q = 1) (hb : d148765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108862, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108863 q = 1) (hb : d148766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108863, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108864 q = 1) (hb : d148767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108864, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108864, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108865 q = 1) (hb : d148768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108865, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108865, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108866 q = 1) (hb : d148769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108866, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108866, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50429 (p : Pattern) (ha : d108873 p = 1) (hb : d149811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108862 q = 1) (hb : d148765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108862, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108863 q = 1) (hb : d148766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108863, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108871 q = 1) (hb : d148767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108871, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108871, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108872 q = 1) (hb : d148768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108872, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108872, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108873 q = 1) (hb : d149811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108873, d149811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108873, d149811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50430 (p : Pattern) (ha : d108883 p = 1) (hb : d149822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149817 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108879 q = 1) (hb : d149818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108879, d149818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108879, d149818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11067 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108880 q = 1) (hb : d149819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108880, d149819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108880, d149819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108881 q = 1) (hb : d149820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108881, d149820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108881, d149820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108882 q = 1) (hb : d149821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108882, d149821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108882, d149821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108883 q = 1) (hb : d149822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108883, d149822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108883, d149822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50431 (p : Pattern) (ha : d108889 p = 1) (hb : d149828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10898 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108867 q = 1) (hb : d148770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108867, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50427 q ha hb
    | true =>
      simp only [d108867, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50428 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108868 q = 1) (hb : d148771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108868, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108868, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108869 q = 1) (hb : d149809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108869, d149809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108869, d149809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108870 q = 1) (hb : d149810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108870, d149810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108870, d149810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108874 q = 1) (hb : d149812 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108874, d149812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108874, d149812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50429 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11008 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108875 q = 1) (hb : d149813 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108875, d149813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108875, d149813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108876 q = 1) (hb : d149814 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108876, d149814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108876, d149814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108877 q = 1) (hb : d149815 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108877, d149815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108877, d149815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108878 q = 1) (hb : d149816 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108878, d149816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108878, d149816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108884 q = 1) (hb : d149823 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108884, d149823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108884, d149823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50430 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108885 q = 1) (hb : d149824 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108885, d149824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108885, d149824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108886 q = 1) (hb : d149825 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108886, d149825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108886, d149825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108887 q = 1) (hb : d149826 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108887, d149826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108887, d149826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108888 q = 1) (hb : d149827 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108888, d149827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108888, d149827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108889 q = 1) (hb : d149828 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108889, d149828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108889, d149828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50432 (p : Pattern) (ha : d108895 p = 1) (hb : d149834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108890 q = 1) (hb : d149829 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108890, d149829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108890, d149829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50431 q ha hb
  have h2 (q : Pattern) (ha : d108891 q = 1) (hb : d149830 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108891, d149830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108891, d149830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108892 q = 1) (hb : d149831 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108892, d149831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108892, d149831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108893 q = 1) (hb : d149832 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108893, d149832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108893, d149832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108894 q = 1) (hb : d149833 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108894, d149833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108894, d149833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108895 q = 1) (hb : d149834 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108895, d149834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108895, d149834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50433 (p : Pattern) (ha : d108901 p = 1) (hb : d148947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148942 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108897 q = 1) (hb : d148943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108897, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11208 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108898 q = 1) (hb : d148944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108898, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108899 q = 1) (hb : d148945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108899, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108900 q = 1) (hb : d148946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108900, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108901 q = 1) (hb : d148947 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108901, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108901, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50434 (p : Pattern) (ha : d108906 p = 1) (hb : d148957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11146 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11155 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11168 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d148942 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108897 q = 1) (hb : d148943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108897, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11208 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108898 q = 1) (hb : d148944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108898, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108899 q = 1) (hb : d148945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108899, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108900 q = 1) (hb : d148946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108900, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11218 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11223 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11225 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d148952 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108902 q = 1) (hb : d148953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108902, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11232 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108903 q = 1) (hb : d148954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108903, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108904 q = 1) (hb : d148955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108904, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108904, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108905 q = 1) (hb : d148956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108905, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108905, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108906 q = 1) (hb : d148957 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108906, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108906, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50435 (p : Pattern) (ha : d108913 p = 1) (hb : d149838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148952 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108902 q = 1) (hb : d148953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108902, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11232 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108903 q = 1) (hb : d148954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108903, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108911 q = 1) (hb : d148955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108911, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108911, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108912 q = 1) (hb : d148956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108912, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108912, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108913 q = 1) (hb : d149838 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108913, d149838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108913, d149838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50436 (p : Pattern) (ha : d108923 p = 1) (hb : d149849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11296 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149844 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108919 q = 1) (hb : d149845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108919, d149845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108919, d149845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11336 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108920 q = 1) (hb : d149846 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108920, d149846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108920, d149846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108921 q = 1) (hb : d149847 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108921, d149847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108921, d149847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108922 q = 1) (hb : d149848 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108922, d149848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108922, d149848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108923 q = 1) (hb : d149849 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108923, d149849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108923, d149849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50437 (p : Pattern) (ha : d108929 p = 1) (hb : d149855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11138 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108907 q = 1) (hb : d148958 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108907, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50433 q ha hb
    | true =>
      simp only [d108907, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50434 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11250 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108908 q = 1) (hb : d148959 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108908, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108908, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108909 q = 1) (hb : d149836 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108909, d149836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108909, d149836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108910 q = 1) (hb : d149837 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108910, d149837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108910, d149837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108914 q = 1) (hb : d149839 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108914, d149839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108914, d149839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50435 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11259 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108915 q = 1) (hb : d149840 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108915, d149840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108915, d149840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108916 q = 1) (hb : d149841 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108916, d149841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108916, d149841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108917 q = 1) (hb : d149842 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108917, d149842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108917, d149842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108918 q = 1) (hb : d149843 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108918, d149843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108918, d149843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108924 q = 1) (hb : d149850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108924, d149850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108924, d149850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50436 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11352 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108925 q = 1) (hb : d149851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108925, d149851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108925, d149851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108926 q = 1) (hb : d149852 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108926, d149852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108926, d149852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108927 q = 1) (hb : d149853 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108927, d149853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108927, d149853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108928 q = 1) (hb : d149854 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108928, d149854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108928, d149854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108929 q = 1) (hb : d149855 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108929, d149855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108929, d149855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50438 (p : Pattern) (ha : d108935 p = 1) (hb : d149861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108930 q = 1) (hb : d149856 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108930, d149856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108930, d149856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50437 q ha hb
  have h2 (q : Pattern) (ha : d108931 q = 1) (hb : d149857 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108931, d149857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108931, d149857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108932 q = 1) (hb : d149858 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108932, d149858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108932, d149858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108933 q = 1) (hb : d149859 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108933, d149859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108933, d149859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108934 q = 1) (hb : d149860 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108934, d149860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108934, d149860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108935 q = 1) (hb : d149861 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108935, d149861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108935, d149861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50439 (p : Pattern) (ha : d108942 p = 1) (hb : d149145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11425 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11438 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d149140 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108938 q = 1) (hb : d149141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108938, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11478 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108939 q = 1) (hb : d149142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108939, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108940 q = 1) (hb : d149143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108940, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108941 q = 1) (hb : d149144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108941, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108942 q = 1) (hb : d149145 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108942, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108942, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50440 (p : Pattern) (ha : d108947 p = 1) (hb : d149155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11425 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11438 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d149140 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108938 q = 1) (hb : d149141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108938, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11478 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108939 q = 1) (hb : d149142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108939, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108940 q = 1) (hb : d149143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108940, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108941 q = 1) (hb : d149144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108941, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11488 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11493 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11495 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d149150 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108943 q = 1) (hb : d149151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108943, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11502 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108944 q = 1) (hb : d149152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108944, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108945 q = 1) (hb : d149153 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108945, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108945, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108946 q = 1) (hb : d149154 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108946, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108946, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108947 q = 1) (hb : d149155 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108947, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108947, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50441 (p : Pattern) (ha : d108954 p = 1) (hb : d149866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108943 q = 1) (hb : d149151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108943, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11502 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108944 q = 1) (hb : d149152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108944, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108952 q = 1) (hb : d149153 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108952, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108952, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108953 q = 1) (hb : d149154 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108953, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108953, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108954 q = 1) (hb : d149866 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108954, d149866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108954, d149866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50442 (p : Pattern) (ha : d108964 p = 1) (hb : d149877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149872 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108960 q = 1) (hb : d149873 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108960, d149873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108960, d149873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11606 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108961 q = 1) (hb : d149874 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108961, d149874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108961, d149874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108962 q = 1) (hb : d149875 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108962, d149875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108962, d149875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108963 q = 1) (hb : d149876 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108963, d149876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108963, d149876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108964 q = 1) (hb : d149877 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108964, d149877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108964, d149877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50443 (p : Pattern) (ha : d108970 p = 1) (hb : d149883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11408 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108948 q = 1) (hb : d149156 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108948, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50439 q ha hb
    | true =>
      simp only [d108948, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50440 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108949 q = 1) (hb : d149157 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108949, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108949, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108950 q = 1) (hb : d149864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108950, d149864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108950, d149864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108951 q = 1) (hb : d149865 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108951, d149865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108951, d149865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108955 q = 1) (hb : d149867 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108955, d149867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108955, d149867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50441 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11529 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108956 q = 1) (hb : d149868 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108956, d149868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108956, d149868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108957 q = 1) (hb : d149869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108957, d149869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108957, d149869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108958 q = 1) (hb : d149870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108958, d149870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108958, d149870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108959 q = 1) (hb : d149871 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108959, d149871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108959, d149871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108965 q = 1) (hb : d149878 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108965, d149878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108965, d149878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50442 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11622 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108966 q = 1) (hb : d149879 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108966, d149879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108966, d149879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108967 q = 1) (hb : d149880 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108967, d149880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108967, d149880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108968 q = 1) (hb : d149881 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108968, d149881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108968, d149881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108969 q = 1) (hb : d149882 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108969, d149882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108969, d149882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108970 q = 1) (hb : d149883 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108970, d149883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108970, d149883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50444 (p : Pattern) (ha : d108976 p = 1) (hb : d149889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108971 q = 1) (hb : d149884 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108971, d149884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108971, d149884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50443 q ha hb
  have h2 (q : Pattern) (ha : d108972 q = 1) (hb : d149885 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108972, d149885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108972, d149885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108973 q = 1) (hb : d149886 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108973, d149886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108973, d149886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108974 q = 1) (hb : d149887 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108974, d149887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108974, d149887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108975 q = 1) (hb : d149888 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108975, d149888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108975, d149888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108976 q = 1) (hb : d149889 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108976, d149889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108976, d149889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50445 (p : Pattern) (ha : d108984 p = 1) (hb : d149353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11696 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11709 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108980 q = 1) (hb : d149349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108980, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11749 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108981 q = 1) (hb : d149350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108981, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108982 q = 1) (hb : d149351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108982, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108983 q = 1) (hb : d149352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108983, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108984 q = 1) (hb : d149353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108984, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108984, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50446 (p : Pattern) (ha : d108989 p = 1) (hb : d149363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11696 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d149348 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108980 q = 1) (hb : d149349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108980, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11749 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108981 q = 1) (hb : d149350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108981, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108982 q = 1) (hb : d149351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108982, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108983 q = 1) (hb : d149352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108983, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11759 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11764 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11766 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d149358 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108985 q = 1) (hb : d149359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108985, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11773 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108986 q = 1) (hb : d149360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108986, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108987 q = 1) (hb : d149361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108987, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108987, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108988 q = 1) (hb : d149362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108988, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108988, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108989 q = 1) (hb : d149363 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108989, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108989, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50447 (p : Pattern) (ha : d108996 p = 1) (hb : d149895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149358 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108985 q = 1) (hb : d149359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108985, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11773 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108986 q = 1) (hb : d149360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108986, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108994 q = 1) (hb : d149361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108994, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108994, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108995 q = 1) (hb : d149362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108995, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108995, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108996 q = 1) (hb : d149895 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108996, d149895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108996, d149895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50448 (p : Pattern) (ha : d109006 p = 1) (hb : d149906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149901 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109002 q = 1) (hb : d149902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109002, d149902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109002, d149902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11877 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109003 q = 1) (hb : d149903 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109003, d149903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109003, d149903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109004 q = 1) (hb : d149904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109004, d149904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109004, d149904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109005 q = 1) (hb : d149905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109005, d149905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109005, d149905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109006 q = 1) (hb : d149906 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109006, d149906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109006, d149906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50449 (p : Pattern) (ha : d109012 p = 1) (hb : d149912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11679 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108990 q = 1) (hb : d149364 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108990, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50445 q ha hb
    | true =>
      simp only [d108990, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50446 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108991 q = 1) (hb : d149365 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108991, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108991, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108992 q = 1) (hb : d149893 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108992, d149893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108992, d149893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108993 q = 1) (hb : d149894 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108993, d149894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108993, d149894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108997 q = 1) (hb : d149896 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108997, d149896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108997, d149896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50447 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11800 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108998 q = 1) (hb : d149897 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108998, d149897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108998, d149897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108999 q = 1) (hb : d149898 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108999, d149898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108999, d149898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d109000 q = 1) (hb : d149899 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109000, d149899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109000, d149899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d109001 q = 1) (hb : d149900 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109001, d149900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109001, d149900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109007 q = 1) (hb : d149907 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109007, d149907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109007, d149907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50448 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11893 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109008 q = 1) (hb : d149908 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109008, d149908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109008, d149908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109009 q = 1) (hb : d149909 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109009, d149909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109009, d149909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d109010 q = 1) (hb : d149910 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109010, d149910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109010, d149910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d109011 q = 1) (hb : d149911 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109011, d149911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109011, d149911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d109012 q = 1) (hb : d149912 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109012, d149912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109012, d149912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50450 (p : Pattern) (ha : d109018 p = 1) (hb : d149918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109013 q = 1) (hb : d149913 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109013, d149913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109013, d149913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50449 q ha hb
  have h2 (q : Pattern) (ha : d109014 q = 1) (hb : d149914 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109014, d149914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109014, d149914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109015 q = 1) (hb : d149915 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109015, d149915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109015, d149915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109016 q = 1) (hb : d149916 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109016, d149916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109016, d149916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109017 q = 1) (hb : d149917 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109017, d149917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109017, d149917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109018 q = 1) (hb : d149918 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109018, d149918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109018, d149918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50451 (p : Pattern) (ha : d109027 p = 1) (hb : d149562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11968 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11981 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109023 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d109023, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12021 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d109024 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109024, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d109025 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109025, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109026 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109026, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109027 q = 1) (hb : d149562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109027, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109027, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50452 (p : Pattern) (ha : d109032 p = 1) (hb : d149572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11959 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d149557 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d109023 q = 1) (hb : d149558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109023, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12021 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d109024 q = 1) (hb : d149559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109024, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d109025 q = 1) (hb : d149560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109025, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109026 q = 1) (hb : d149561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109026, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12031 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12036 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12038 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d149567 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d109028 q = 1) (hb : d149568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d109028, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12045 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109029 q = 1) (hb : d149569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109029, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109030 q = 1) (hb : d149570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109030, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d109030, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109031 q = 1) (hb : d149571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109031, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d109031, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d109032 q = 1) (hb : d149572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109032, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109032, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro50453 (p : Pattern) (ha : d109039 p = 1) (hb : d149925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149567 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109028 q = 1) (hb : d149568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109028, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109029 q = 1) (hb : d149569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109029, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109037 q = 1) (hb : d149570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109037, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109037, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109038 q = 1) (hb : d149571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109038, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109038, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109039 q = 1) (hb : d149925 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109039, d149925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109039, d149925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50454 (p : Pattern) (ha : d109049 p = 1) (hb : d149936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d149931 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109045 q = 1) (hb : d149932 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109045, d149932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109045, d149932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12149 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109046 q = 1) (hb : d149933 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109046, d149933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109046, d149933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109047 q = 1) (hb : d149934 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109047, d149934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109047, d149934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109048 q = 1) (hb : d149935 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109048, d149935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109048, d149935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109049 q = 1) (hb : d149936 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109049, d149936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109049, d149936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50455 (p : Pattern) (ha : d109055 p = 1) (hb : d149942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109033 q = 1) (hb : d149573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109033, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50451 q ha hb
    | true =>
      simp only [d109033, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50452 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109034 q = 1) (hb : d149574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109034, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109034, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109035 q = 1) (hb : d149923 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109035, d149923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109035, d149923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109036 q = 1) (hb : d149924 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109036, d149924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109036, d149924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109040 q = 1) (hb : d149926 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109040, d149926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109040, d149926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50453 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12072 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d109041 q = 1) (hb : d149927 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109041, d149927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109041, d149927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d109042 q = 1) (hb : d149928 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109042, d149928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109042, d149928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d109043 q = 1) (hb : d149929 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109043, d149929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109043, d149929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d109044 q = 1) (hb : d149930 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109044, d149930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109044, d149930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109050 q = 1) (hb : d149937 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109050, d149937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109050, d149937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50454 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12165 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109051 q = 1) (hb : d149938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109051, d149938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109051, d149938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109052 q = 1) (hb : d149939 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109052, d149939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109052, d149939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d109053 q = 1) (hb : d149940 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109053, d149940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109053, d149940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d109054 q = 1) (hb : d149941 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109054, d149941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109054, d149941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d109055 q = 1) (hb : d149942 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109055, d149942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109055, d149942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50456 (p : Pattern) (ha : d109061 p = 1) (hb : d149948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109056 q = 1) (hb : d149943 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109056, d149943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109056, d149943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50455 q ha hb
  have h2 (q : Pattern) (ha : d109057 q = 1) (hb : d149944 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109057, d149944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109057, d149944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109058 q = 1) (hb : d149945 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109058, d149945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109058, d149945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109059 q = 1) (hb : d149946 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109059, d149946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109059, d149946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109060 q = 1) (hb : d149947 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109060, d149947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109060, d149947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109061 q = 1) (hb : d149948 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109061, d149948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109061, d149948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50457 (p : Pattern) (ha : d109067 p = 1) (hb : d149954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d108896 q = 1) (hb : d149835 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108896, d149835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50426 q ha hb
    | true =>
      simp only [d108896, d149835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50432 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108936 q = 1) (hb : d149862 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108936, d149862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108936, d149862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50438 q ha hb
  have h3 (q : Pattern) (ha : d108937 q = 1) (hb : d149863 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108937, d149863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108937, d149863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108977 q = 1) (hb : d149890 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108977, d149890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108977, d149890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50444 q ha hb
  have h5 (q : Pattern) (ha : d108978 q = 1) (hb : d149891 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108978, d149891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108978, d149891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108979 q = 1) (hb : d149892 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108979, d149892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108979, d149892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109019 q = 1) (hb : d149919 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109019, d149919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109019, d149919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50450 q ha hb
  have h8 (q : Pattern) (ha : d109020 q = 1) (hb : d149920 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109020, d149920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109020, d149920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109021 q = 1) (hb : d149921 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109021, d149921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109021, d149921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109022 q = 1) (hb : d149922 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109022, d149922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109022, d149922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109062 q = 1) (hb : d149949 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109062, d149949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109062, d149949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50456 q ha hb
  have h12 (q : Pattern) (ha : d109063 q = 1) (hb : d149950 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109063, d149950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109063, d149950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109064 q = 1) (hb : d149951 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109064, d149951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109064, d149951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109065 q = 1) (hb : d149952 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109065, d149952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109065, d149952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109066 q = 1) (hb : d149953 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109066, d149953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109066, d149953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109067 q = 1) (hb : d149954 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109067, d149954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109067, d149954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro50458 (p : Pattern) (ha : d109073 p = 1) (hb : d149960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109068 q = 1) (hb : d149955 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109068, d149955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50457 q ha hb
    | true =>
      simp only [d109068, d149955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109069 q = 1) (hb : d149956 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109069, d149956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109069, d149956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109070 q = 1) (hb : d149957 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109070, d149957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109070, d149957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109071 q = 1) (hb : d149958 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109071, d149958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109071, d149958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109072 q = 1) (hb : d149959 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109072, d149959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109072, d149959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109073 q = 1) (hb : d149960 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109073, d149960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109073, d149960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50459 (p : Pattern) (ha : d109079 p = 1) (hb : d149966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109074 q = 1) (hb : d149961 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109074, d149961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50458 q ha hb
    | true =>
      simp only [d109074, d149961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109075 q = 1) (hb : d149962 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109075, d149962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109075, d149962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109076 q = 1) (hb : d149963 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109076, d149963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109076, d149963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109077 q = 1) (hb : d149964 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109077, d149964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109077, d149964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109078 q = 1) (hb : d149965 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109078, d149965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109078, d149965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109079 q = 1) (hb : d149966 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109079, d149966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109079, d149966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50460 (p : Pattern) (ha : d109085 p = 1) (hb : d149972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109080 q = 1) (hb : d149967 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109080, d149967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50459 q ha hb
    | true =>
      simp only [d109080, d149967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109081 q = 1) (hb : d149968 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109081, d149968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109081, d149968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109082 q = 1) (hb : d149969 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109082, d149969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109082, d149969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109083 q = 1) (hb : d149970 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109083, d149970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109083, d149970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109084 q = 1) (hb : d149971 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109084, d149971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109084, d149971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109085 q = 1) (hb : d149972 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109085, d149972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109085, d149972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50461 (p : Pattern) (ha : d109091 p = 1) (hb : d149978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109086 q = 1) (hb : d149973 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109086, d149973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50460 q ha hb
    | true =>
      simp only [d109086, d149973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109087 q = 1) (hb : d149974 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109087, d149974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109087, d149974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109088 q = 1) (hb : d149975 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109088, d149975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109088, d149975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109089 q = 1) (hb : d149976 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109089, d149976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109089, d149976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109090 q = 1) (hb : d149977 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109090, d149977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109090, d149977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109091 q = 1) (hb : d149978 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109091, d149978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109091, d149978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50462 (p : Pattern) (ha : d109097 p = 1) (hb : d149984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109092 q = 1) (hb : d149979 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109092, d149979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50461 q ha hb
    | true =>
      simp only [d109092, d149979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109093 q = 1) (hb : d149980 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109093, d149980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109093, d149980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109094 q = 1) (hb : d149981 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109094, d149981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109094, d149981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109095 q = 1) (hb : d149982 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109095, d149982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109095, d149982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109096 q = 1) (hb : d149983 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109096, d149983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109096, d149983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109097 q = 1) (hb : d149984 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109097, d149984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109097, d149984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50463 (p : Pattern) (ha : d109103 p = 1) (hb : d149990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109098 q = 1) (hb : d149985 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109098, d149985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50462 q ha hb
    | true =>
      simp only [d109098, d149985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109099 q = 1) (hb : d149986 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109099, d149986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109099, d149986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109100 q = 1) (hb : d149987 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109100, d149987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109100, d149987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109101 q = 1) (hb : d149988 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109101, d149988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109101, d149988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109102 q = 1) (hb : d149989 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109102, d149989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109102, d149989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109103 q = 1) (hb : d149990 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109103, d149990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109103, d149990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50464 (p : Pattern) (ha : d109109 p = 1) (hb : d149996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109104 q = 1) (hb : d149991 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109104, d149991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50463 q ha hb
    | true =>
      simp only [d109104, d149991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109105 q = 1) (hb : d149992 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109105, d149992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109105, d149992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109106 q = 1) (hb : d149993 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109106, d149993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109106, d149993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109107 q = 1) (hb : d149994 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109107, d149994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109107, d149994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109108 q = 1) (hb : d149995 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109108, d149995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109108, d149995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109109 q = 1) (hb : d149996 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109109, d149996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109109, d149996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50465 (p : Pattern) (ha : d750 p = 1) (hb : d208035 p = 1) : d200353 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d136 q = 1) (hb : d208034 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d137 q = 1) (hb : d208034 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d750 q = 1) (hb : d208035 q = 1) : d200353 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d750, d208035, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d750, d208035, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50466 (p : Pattern) (ha : d20893 p = 1) (hb : d208035 p = 1) : d200533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50465 q ha hb
    | true =>
      simp only [d751, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d208035 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d208035 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d208035 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20892 q = 1) (hb : d208035 q = 1) : d200358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20892, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20892, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d208035 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20893 q = 1) (hb : d208035 q = 1) : d200533 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20893, d200533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20893, d200533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50467 (p : Pattern) (ha : d20899 p = 1) (hb : d208035 p = 1) : d209547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d208035 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20894 q = 1) (hb : d208035 q = 1) : d209542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50466 q ha hb
    | true =>
      simp only [d20894, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20895 q = 1) (hb : d208035 q = 1) : d209543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20896 q = 1) (hb : d208035 q = 1) : d209544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d208035 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20897 q = 1) (hb : d208035 q = 1) : d209545 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d209545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20897, d209545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d208035 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20898 q = 1) (hb : d208035 q = 1) : d209546 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20898, d209546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20898, d209546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20899 q = 1) (hb : d208035 q = 1) : d209547 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20899, d209547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20899, d209547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro50468 (p : Pattern) (ha : d20905 p = 1) (hb : d208035 p = 1) : d209553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50467 q ha hb
    | true =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d208035 q = 1) : d209551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20904 q = 1) (hb : d208035 q = 1) : d209552 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d209552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20904, d209552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20905 q = 1) (hb : d208035 q = 1) : d209553 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20905, d209553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20905, d209553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro50469 (p : Pattern) (ha : d150001 p = 1) (hb : d208035 p = 1) : d209559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d208035 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d208035 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d208035 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20906 q = 1) (hb : d208035 q = 1) : d209554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50468 q ha hb
    | true =>
      simp only [d20906, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d149997 q = 1) (hb : d208035 q = 1) : d209555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d209555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149997, d209555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d208035 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d149998 q = 1) (hb : d208035 q = 1) : d209556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d209556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149998, d209556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149999 q = 1) (hb : d208035 q = 1) : d209557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d209557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149999, d209557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150000 q = 1) (hb : d208035 q = 1) : d209558 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d209558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150000, d209558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150001 q = 1) (hb : d208035 q = 1) : d209559 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150001, d209559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150001, d209559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50470 (p : Pattern) (ha : d20912 p = 1) (hb : d208035 p = 1) : d209560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50467 q ha hb
    | true =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d208035 q = 1) : d209551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20904 q = 1) (hb : d208035 q = 1) : d209552 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d209552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20904, d209552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20912 q = 1) (hb : d208035 q = 1) : d209560 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20912, d209560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20912, d209560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro50471 (p : Pattern) (ha : d150006 p = 1) (hb : d208035 p = 1) : d209566 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d208035 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d208035 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d208035 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20906 q = 1) (hb : d208035 q = 1) : d209554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50468 q ha hb
    | true =>
      simp only [d20906, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149997 q = 1) (hb : d208035 q = 1) : d209555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d209555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149997, d209555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d208035 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d149998 q = 1) (hb : d208035 q = 1) : d209556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d209556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149998, d209556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149999 q = 1) (hb : d208035 q = 1) : d209557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d209557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149999, d209557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150000 q = 1) (hb : d208035 q = 1) : d209558 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d209558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150000, d209558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d208035 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d208035 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d208035 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20913 q = 1) (hb : d208035 q = 1) : d209561 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50470 q ha hb
    | true =>
      simp only [d20913, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150002 q = 1) (hb : d208035 q = 1) : d209562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d209562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150002, d209562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d208035 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d150003 q = 1) (hb : d208035 q = 1) : d209563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d209563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150003, d209563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150004 q = 1) (hb : d208035 q = 1) : d209564 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150004, d209564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150004, d209564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150005 q = 1) (hb : d208035 q = 1) : d209565 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150005, d209565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150005, d209565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d150006 q = 1) (hb : d208035 q = 1) : d209566 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150006, d209566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150006, d209566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro50472 (p : Pattern) (ha : d150013 p = 1) (hb : d208035 p = 1) : d209573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d208035 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20913 q = 1) (hb : d208035 q = 1) : d209561 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50470 q ha hb
    | true =>
      simp only [d20913, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150002 q = 1) (hb : d208035 q = 1) : d209562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d209562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150002, d209562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d208035 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150003 q = 1) (hb : d208035 q = 1) : d209563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d209563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150003, d209563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150011 q = 1) (hb : d208035 q = 1) : d209571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150011, d209571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150011, d209571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150012 q = 1) (hb : d208035 q = 1) : d209572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150012, d209572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150012, d209572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150013 q = 1) (hb : d208035 q = 1) : d209573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150013, d209573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150013, d209573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50473 (p : Pattern) (ha : d20932 p = 1) (hb : d208035 p = 1) : d200620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d208035 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50465 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50465 q ha hb
    | true =>
      simp only [d751, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d208035 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d208035 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d208035 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d208035 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20931 q = 1) (hb : d208035 q = 1) : d200426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20931, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20931, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d208035 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20932 q = 1) (hb : d208035 q = 1) : d200620 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20932, d200620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20932, d200620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro50474 (p : Pattern) (ha : d20938 p = 1) (hb : d208035 p = 1) : d209584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d208035 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20933 q = 1) (hb : d208035 q = 1) : d209579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50473 q ha hb
    | true =>
      simp only [d20933, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20934 q = 1) (hb : d208035 q = 1) : d209580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20935 q = 1) (hb : d208035 q = 1) : d209581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d208035 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20936 q = 1) (hb : d208035 q = 1) : d209582 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d209582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20936, d209582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d208035 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20937 q = 1) (hb : d208035 q = 1) : d209583 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20937, d209583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20937, d209583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20938 q = 1) (hb : d208035 q = 1) : d209584 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20938, d209584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20938, d209584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro50475 (p : Pattern) (ha : d20944 p = 1) (hb : d208035 p = 1) : d209590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d208035 q = 1) : d209585 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50474 q ha hb
    | true =>
      simp only [d20939, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d208035 q = 1) : d209586 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d208035 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20941 q = 1) (hb : d208035 q = 1) : d209587 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20941, d209587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20941, d209587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20942 q = 1) (hb : d208035 q = 1) : d209588 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20942, d209588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20942, d209588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20943 q = 1) (hb : d208035 q = 1) : d209589 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20943, d209589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20943, d209589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20944 q = 1) (hb : d208035 q = 1) : d209590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20944, d209590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20944, d209590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro50476 (p : Pattern) (ha : d150023 p = 1) (hb : d208035 p = 1) : d209596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d208035 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20945 q = 1) (hb : d208035 q = 1) : d209591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d209591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50475 q ha hb
    | true =>
      simp only [d20945, d209591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150019 q = 1) (hb : d208035 q = 1) : d209592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150019, d209592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150019, d209592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d208035 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150020 q = 1) (hb : d208035 q = 1) : d209593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150020, d209593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150020, d209593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150021 q = 1) (hb : d208035 q = 1) : d209594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150021, d209594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150021, d209594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150022 q = 1) (hb : d208035 q = 1) : d209595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150022, d209595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150022, d209595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150023 q = 1) (hb : d208035 q = 1) : d209596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150023, d209596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150023, d209596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50477 (p : Pattern) (ha : d150029 p = 1) (hb : d208035 p = 1) : d209602 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d208035 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150007 q = 1) (hb : d208035 q = 1) : d209567 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150007, d209567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50469 q ha hb
    | true =>
      simp only [d150007, d209567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50471 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d208035 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150008 q = 1) (hb : d208035 q = 1) : d209568 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150008, d209568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150008, d209568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150009 q = 1) (hb : d208035 q = 1) : d209569 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150009, d209569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150009, d209569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150010 q = 1) (hb : d208035 q = 1) : d209570 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150010, d209570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150010, d209570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150014 q = 1) (hb : d208035 q = 1) : d209574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150014, d209574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150014, d209574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50472 q ha hb
  have h8 (q : Pattern) (ha : d150015 q = 1) (hb : d208035 q = 1) : d209575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150015, d209575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150015, d209575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d150016 q = 1) (hb : d208035 q = 1) : d209576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150016, d209576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150016, d209576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d150017 q = 1) (hb : d208035 q = 1) : d209577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150017, d209577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150017, d209577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150018 q = 1) (hb : d208035 q = 1) : d209578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150018, d209578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150018, d209578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150024 q = 1) (hb : d208035 q = 1) : d209597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150024, d209597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150024, d209597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50476 q ha hb
  have h13 (q : Pattern) (ha : d150025 q = 1) (hb : d208035 q = 1) : d209598 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150025, d209598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150025, d209598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d150026 q = 1) (hb : d208035 q = 1) : d209599 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150026, d209599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150026, d209599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d150027 q = 1) (hb : d208035 q = 1) : d209600 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150027, d209600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150027, d209600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d150028 q = 1) (hb : d208035 q = 1) : d209601 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150028, d209601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150028, d209601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150029 q = 1) (hb : d208035 q = 1) : d209602 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150029, d209602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150029, d209602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro50478 (p : Pattern) (ha : d20966 p = 1) (hb : d208035 p = 1) : d209612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208035 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d208035 q = 1) : d209554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50468 q ha hb
    | true =>
      simp only [d20906, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d208035 q = 1) : d209608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d208035 q = 1) : d209609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d208035 q = 1) : d209610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d208035 q = 1) : d209611 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20966 q = 1) (hb : d208035 q = 1) : d209612 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20966, d209612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20966, d209612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro50479 (p : Pattern) (ha : d20973 p = 1) (hb : d208035 p = 1) : d209619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208035 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d208035 q = 1) : d209554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50468 q ha hb
    | true =>
      simp only [d20906, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d208035 q = 1) : d209608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d208035 q = 1) : d209609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d208035 q = 1) : d209610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d208035 q = 1) : d209611 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d208035 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20913 q = 1) (hb : d208035 q = 1) : d209561 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50470 q ha hb
    | true =>
      simp only [d20913, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20969 q = 1) (hb : d208035 q = 1) : d209615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20970 q = 1) (hb : d208035 q = 1) : d209616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20970, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20971 q = 1) (hb : d208035 q = 1) : d209617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d20972 q = 1) (hb : d208035 q = 1) : d209618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20973 q = 1) (hb : d208035 q = 1) : d209619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20973, d209619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20973, d209619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro50480 (p : Pattern) (ha : d21058 p = 1) (hb : d208035 p = 1) : d209680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208035 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d208035 q = 1) : d209554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50468 q ha hb
    | true =>
      simp only [d20906, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d208035 q = 1) : d209608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d208035 q = 1) : d209609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d208035 q = 1) : d209610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d208035 q = 1) : d209611 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d208035 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d21058 q = 1) (hb : d208035 q = 1) : d209680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21058, d209680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21058, d209680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50481 (p : Pattern) (ha : d20978 p = 1) (hb : d208035 p = 1) : d209624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50467 q ha hb
    | true =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d208035 q = 1) : d209551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20977 q = 1) (hb : d208035 q = 1) : d209623 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d209623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d209623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20978 q = 1) (hb : d208035 q = 1) : d209624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20978, d209624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20978, d209624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro50482 (p : Pattern) (ha : d20985 p = 1) (hb : d208035 p = 1) : d209631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50467 q ha hb
    | true =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20983 q = 1) (hb : d208035 q = 1) : d209629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d209629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d209629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20984 q = 1) (hb : d208035 q = 1) : d209630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d209630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20984, d209630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20985 q = 1) (hb : d208035 q = 1) : d209631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20985, d209631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20985, d209631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro50483 (p : Pattern) (ha : d5450 p = 1) (hb : d208035 p = 1) : d200353 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5448 q = 1) (hb : d208034 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5448, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5449 q = 1) (hb : d208034 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5450 q = 1) (hb : d208035 q = 1) : d200353 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5450, d208035, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5450, d208035, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro50484 (p : Pattern) (ha : d20989 p = 1) (hb : d208035 p = 1) : d200523 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d314 q = 1) : d314 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315 q = 1) (hb : d152852 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d135 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d316 q = 1) (hb : d208034 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d317 q = 1) (hb : d208034 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d317, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20989 q = 1) (hb : d208035 q = 1) : d200523 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d20989, d208035, d200523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20989, d208035, d200523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50485 (p : Pattern) (ha : d20996 p = 1) (hb : d208035 p = 1) : d209635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50484 q ha hb
    | true =>
      simp only [d20990, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d208035 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d208035 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50465 q ha hb
    | true =>
      simp only [d751, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d208035 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d208035 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20994 q = 1) (hb : d208035 q = 1) : d200528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20994, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5451 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50483 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5452 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5453 q = 1) (hb : d208035 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5454 q = 1) (hb : d208035 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d208035 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20995 q = 1) (hb : d208035 q = 1) : d200358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20995, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20995, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d20996 q = 1) (hb : d208035 q = 1) : d209635 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20996, d209635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20996, d209635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro50486 (p : Pattern) (ha : d21002 p = 1) (hb : d208035 p = 1) : d209641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d208035 q = 1) : d209636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d209636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50485 q ha hb
    | true =>
      simp only [d20997, d209636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50466 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d208035 q = 1) : d209637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d209637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d209637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d208035 q = 1) : d209638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d209638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d209638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d208035 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20894 q = 1) (hb : d208035 q = 1) : d209542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50466 q ha hb
    | true =>
      simp only [d20894, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20895 q = 1) (hb : d208035 q = 1) : d209543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20896 q = 1) (hb : d208035 q = 1) : d209544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21000 q = 1) (hb : d208035 q = 1) : d209639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d209639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d209639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d208035 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20897 q = 1) (hb : d208035 q = 1) : d209545 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d209545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20897, d209545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21001 q = 1) (hb : d208035 q = 1) : d209640 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21001, d209640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21001, d209640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21002 q = 1) (hb : d208035 q = 1) : d209641 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21002, d209641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21002, d209641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro50487 (p : Pattern) (ha : d21008 p = 1) (hb : d208035 p = 1) : d209647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d208035 q = 1) : d209642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d209642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50486 q ha hb
    | true =>
      simp only [d21003, d209642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d208035 q = 1) : d209643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d209643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d209643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50467 q ha hb
    | true =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d208035 q = 1) : d209644 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d209644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d209644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d208035 q = 1) : d209645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d209645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d209645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d208035 q = 1) : d209646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d209646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d209646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21008 q = 1) (hb : d208035 q = 1) : d209647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21008, d209647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21008, d209647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50488 (p : Pattern) (ha : d21029 p = 1) (hb : d208035 p = 1) : d209653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50467 q ha hb
    | true =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d208035 q = 1) : d209650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d209650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d209650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d208035 q = 1) : d209651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d209651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d209651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d208035 q = 1) : d209652 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d209652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d209652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21029 q = 1) (hb : d208035 q = 1) : d209653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21029, d209653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21029, d209653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50489 (p : Pattern) (ha : d150039 p = 1) (hb : d208035 p = 1) : d209659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d208035 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20979 q = 1) (hb : d208035 q = 1) : d209625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d209625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50481 q ha hb
    | true =>
      simp only [d20979, d209625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20980 q = 1) (hb : d208035 q = 1) : d209626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d209626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d209626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20981 q = 1) (hb : d208035 q = 1) : d209627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d209627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20981, d209627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20982 q = 1) (hb : d208035 q = 1) : d209628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d209628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d209628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d208035 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20986 q = 1) (hb : d208035 q = 1) : d209632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d209632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50482 q ha hb
    | true =>
      simp only [d20986, d209632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20987 q = 1) (hb : d208035 q = 1) : d209633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d209633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d209633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20988 q = 1) (hb : d208035 q = 1) : d209634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d209634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20988, d209634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21009 q = 1) (hb : d208035 q = 1) : d209648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d209648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50487 q ha hb
    | true =>
      simp only [d21009, d209648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50468 q ha hb
  have h11 (q : Pattern) (ha : d150035 q = 1) (hb : d208035 q = 1) : d209649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d209649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150035, d209649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21030 q = 1) (hb : d208035 q = 1) : d209654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d209654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50488 q ha hb
    | true =>
      simp only [d21030, d209654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21031 q = 1) (hb : d208035 q = 1) : d209655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d209655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21031, d209655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150036 q = 1) (hb : d208035 q = 1) : d209656 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d209656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150036, d209656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150037 q = 1) (hb : d208035 q = 1) : d209657 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d209657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150037, d209657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150038 q = 1) (hb : d208035 q = 1) : d209658 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d209658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150038, d209658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150039 q = 1) (hb : d208035 q = 1) : d209659 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150039, d209659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150039, d209659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro50490 (p : Pattern) (ha : d21036 p = 1) (hb : d208035 p = 1) : d209660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50467 q ha hb
    | true =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d208035 q = 1) : d209551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20977 q = 1) (hb : d208035 q = 1) : d209623 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d209623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d209623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21036 q = 1) (hb : d208035 q = 1) : d209660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21036, d209660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21036, d209660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro50491 (p : Pattern) (ha : d21041 p = 1) (hb : d208035 p = 1) : d209665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50467 q ha hb
    | true =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20983 q = 1) (hb : d208035 q = 1) : d209629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d209629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d209629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20984 q = 1) (hb : d208035 q = 1) : d209630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d209630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20984, d209630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21041 q = 1) (hb : d208035 q = 1) : d209665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21041, d209665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21041, d209665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro50492 (p : Pattern) (ha : d21045 p = 1) (hb : d208035 p = 1) : d209669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d208035 q = 1) : d209642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d209642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50486 q ha hb
    | true =>
      simp only [d21003, d209642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d208035 q = 1) : d209643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d209643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d209643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50467 q ha hb
    | true =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d208035 q = 1) : d209644 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d209644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d209644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d208035 q = 1) : d209645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d209645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d209645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d208035 q = 1) : d209646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d209646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d209646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21045 q = 1) (hb : d208035 q = 1) : d209669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21045, d209669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21045, d209669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50493 (p : Pattern) (ha : d21050 p = 1) (hb : d208035 p = 1) : d209672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50467 q ha hb
    | true =>
      simp only [d20900, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d208035 q = 1) : d209650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d209650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d209650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d208035 q = 1) : d209651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d209651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d209651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d208035 q = 1) : d209652 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d209652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d209652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21050 q = 1) (hb : d208035 q = 1) : d209672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21050, d209672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21050, d209672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50494 (p : Pattern) (ha : d150044 p = 1) (hb : d208035 p = 1) : d209678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d208035 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20979 q = 1) (hb : d208035 q = 1) : d209625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d209625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50481 q ha hb
    | true =>
      simp only [d20979, d209625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20980 q = 1) (hb : d208035 q = 1) : d209626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d209626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d209626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20981 q = 1) (hb : d208035 q = 1) : d209627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d209627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20981, d209627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20982 q = 1) (hb : d208035 q = 1) : d209628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d209628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d209628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d208035 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20986 q = 1) (hb : d208035 q = 1) : d209632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d209632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50482 q ha hb
    | true =>
      simp only [d20986, d209632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20987 q = 1) (hb : d208035 q = 1) : d209633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d209633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d209633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20988 q = 1) (hb : d208035 q = 1) : d209634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d209634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20988, d209634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21009 q = 1) (hb : d208035 q = 1) : d209648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d209648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50487 q ha hb
    | true =>
      simp only [d21009, d209648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50468 q ha hb
  have h11 (q : Pattern) (ha : d150035 q = 1) (hb : d208035 q = 1) : d209649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d209649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150035, d209649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21030 q = 1) (hb : d208035 q = 1) : d209654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d209654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50488 q ha hb
    | true =>
      simp only [d21030, d209654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21031 q = 1) (hb : d208035 q = 1) : d209655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d209655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21031, d209655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150036 q = 1) (hb : d208035 q = 1) : d209656 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d209656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150036, d209656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150037 q = 1) (hb : d208035 q = 1) : d209657 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d209657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150037, d209657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150038 q = 1) (hb : d208035 q = 1) : d209658 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d209658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150038, d209658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d208035 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d21037 q = 1) (hb : d208035 q = 1) : d209661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21037, d209661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50490 q ha hb
    | true =>
      simp only [d21037, d209661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21038 q = 1) (hb : d208035 q = 1) : d209662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21038, d209662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21038, d209662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d21039 q = 1) (hb : d208035 q = 1) : d209663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21039, d209663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21039, d209663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d21040 q = 1) (hb : d208035 q = 1) : d209664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21040, d209664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21040, d209664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d208035 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d21042 q = 1) (hb : d208035 q = 1) : d209666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21042, d209666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50491 q ha hb
    | true =>
      simp only [d21042, d209666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d21043 q = 1) (hb : d208035 q = 1) : d209667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21043, d209667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21043, d209667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d21044 q = 1) (hb : d208035 q = 1) : d209668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21044, d209668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21044, d209668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21046 q = 1) (hb : d208035 q = 1) : d209670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d209670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50492 q ha hb
    | true =>
      simp only [d21046, d209670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50470 q ha hb
  have h27 (q : Pattern) (ha : d150040 q = 1) (hb : d208035 q = 1) : d209671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d209671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d150040, d209671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d21051 q = 1) (hb : d208035 q = 1) : d209673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d209673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50493 q ha hb
    | true =>
      simp only [d21051, d209673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d21052 q = 1) (hb : d208035 q = 1) : d209674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d209674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d21052, d209674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d150041 q = 1) (hb : d208035 q = 1) : d209675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d209675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d150041, d209675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d150042 q = 1) (hb : d208035 q = 1) : d209676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150042, d209676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d150042, d209676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d150043 q = 1) (hb : d208035 q = 1) : d209677 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150043, d209677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150043, d209677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d150044 q = 1) (hb : d208035 q = 1) : d209678 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150044, d209678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150044, d209678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro50495 (p : Pattern) (ha : d150051 p = 1) (hb : d208035 p = 1) : d209687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21046 q = 1) (hb : d208035 q = 1) : d209670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d209670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50492 q ha hb
    | true =>
      simp only [d21046, d209670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50470 q ha hb
  have h2 (q : Pattern) (ha : d150040 q = 1) (hb : d208035 q = 1) : d209671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d209671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150040, d209671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21051 q = 1) (hb : d208035 q = 1) : d209673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d209673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50493 q ha hb
    | true =>
      simp only [d21051, d209673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21052 q = 1) (hb : d208035 q = 1) : d209674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d209674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21052, d209674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150041 q = 1) (hb : d208035 q = 1) : d209675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d209675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150041, d209675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150049 q = 1) (hb : d208035 q = 1) : d209685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150049, d209685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150049, d209685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150050 q = 1) (hb : d208035 q = 1) : d209686 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150050, d209686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150050, d209686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150051 q = 1) (hb : d208035 q = 1) : d209687 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150051, d209687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150051, d209687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50496 (p : Pattern) (ha : d21077 p = 1) (hb : d208035 p = 1) : d209693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d208035 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50484 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50484 q ha hb
    | true =>
      simp only [d20990, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d208035 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d208035 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d208035 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d208035 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50465 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50465 q ha hb
    | true =>
      simp only [d751, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d208035 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d208035 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d208035 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21075 q = 1) (hb : d208035 q = 1) : d200615 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21075, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5495 q = 1) (hb : d208035 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50483 q ha hb
  have h15 (q : Pattern) (ha : d5451 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50483 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5496 q = 1) (hb : d208035 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5452 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5497 q = 1) (hb : d208035 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5498 q = 1) (hb : d208035 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d208035 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d21076 q = 1) (hb : d208035 q = 1) : d200426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21076, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21076, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d21077 q = 1) (hb : d208035 q = 1) : d209693 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21077, d209693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21077, d209693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro50497 (p : Pattern) (ha : d21083 p = 1) (hb : d208035 p = 1) : d209699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d208035 q = 1) : d209694 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d209694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50496 q ha hb
    | true =>
      simp only [d21078, d209694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50473 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d208035 q = 1) : d209695 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d209695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d209695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d208035 q = 1) : d209696 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d209696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d209696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d208035 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20933 q = 1) (hb : d208035 q = 1) : d209579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50473 q ha hb
    | true =>
      simp only [d20933, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20934 q = 1) (hb : d208035 q = 1) : d209580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20935 q = 1) (hb : d208035 q = 1) : d209581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21081 q = 1) (hb : d208035 q = 1) : d209697 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d209697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d209697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d208035 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20936 q = 1) (hb : d208035 q = 1) : d209582 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d209582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20936, d209582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21082 q = 1) (hb : d208035 q = 1) : d209698 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21082, d209698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21082, d209698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21083 q = 1) (hb : d208035 q = 1) : d209699 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21083, d209699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21083, d209699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro50498 (p : Pattern) (ha : d21089 p = 1) (hb : d208035 p = 1) : d209705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21084 q = 1) (hb : d208035 q = 1) : d209700 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21084, d209700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50497 q ha hb
    | true =>
      simp only [d21084, d209700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21085 q = 1) (hb : d208035 q = 1) : d209701 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21085, d209701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21085, d209701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20939 q = 1) (hb : d208035 q = 1) : d209585 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50474 q ha hb
    | true =>
      simp only [d20939, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20940 q = 1) (hb : d208035 q = 1) : d209586 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21086 q = 1) (hb : d208035 q = 1) : d209702 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21086, d209702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21086, d209702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21087 q = 1) (hb : d208035 q = 1) : d209703 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21087, d209703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21087, d209703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21088 q = 1) (hb : d208035 q = 1) : d209704 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21088, d209704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21088, d209704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21089 q = 1) (hb : d208035 q = 1) : d209705 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21089, d209705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21089, d209705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50499 (p : Pattern) (ha : d21110 p = 1) (hb : d208035 p = 1) : d209711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d208035 q = 1) : d209585 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50474 q ha hb
    | true =>
      simp only [d20939, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d208035 q = 1) : d209586 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21107 q = 1) (hb : d208035 q = 1) : d209708 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21107, d209708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21107, d209708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21108 q = 1) (hb : d208035 q = 1) : d209709 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21108, d209709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21108, d209709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21109 q = 1) (hb : d208035 q = 1) : d209710 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21109, d209710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21109, d209710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21110 q = 1) (hb : d208035 q = 1) : d209711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21110, d209711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21110, d209711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
