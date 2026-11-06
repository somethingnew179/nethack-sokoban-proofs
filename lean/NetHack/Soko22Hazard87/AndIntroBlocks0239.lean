import NetHack.Soko22Hazard87.AndIntroBlocks0238
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro59750 (p : Pattern) (ha : d74533 p = 1) (hb : d211369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d74173 q = 1) (hb : d211198 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74173, d211198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59524 q ha hb
    | true =>
      simp only [d74173, d211198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59553 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74258 q = 1) (hb : d211238 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74258, d211238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74258, d211238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59588 q ha hb
  have h3 (q : Pattern) (ha : d74259 q = 1) (hb : d211239 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74259, d211239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74259, d211239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74347 q = 1) (hb : d211279 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74347, d211279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74347, d211279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59642 q ha hb
  have h5 (q : Pattern) (ha : d74348 q = 1) (hb : d211280 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74348, d211280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74348, d211280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74349 q = 1) (hb : d211281 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74349, d211281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74349, d211281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74437 q = 1) (hb : d211321 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74437, d211321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74437, d211321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59696 q ha hb
  have h8 (q : Pattern) (ha : d74438 q = 1) (hb : d211322 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74438, d211322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74438, d211322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74439 q = 1) (hb : d211323 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74439, d211323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74439, d211323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74440 q = 1) (hb : d211324 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74440, d211324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74440, d211324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74528 q = 1) (hb : d211364 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74528, d211364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74528, d211364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59749 q ha hb
  have h12 (q : Pattern) (ha : d74529 q = 1) (hb : d211365 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74529, d211365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74529, d211365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74530 q = 1) (hb : d211366 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74530, d211366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74530, d211366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74531 q = 1) (hb : d211367 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74531, d211367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74531, d211367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74532 q = 1) (hb : d211368 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74532, d211368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74532, d211368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74533 q = 1) (hb : d211369 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74533, d211369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74533, d211369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro59751 (p : Pattern) (ha : d74539 p = 1) (hb : d211375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74534 q = 1) (hb : d211370 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74534, d211370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59750 q ha hb
    | true =>
      simp only [d74534, d211370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74535 q = 1) (hb : d211371 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74535, d211371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74535, d211371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74536 q = 1) (hb : d211372 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74536, d211372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74536, d211372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74537 q = 1) (hb : d211373 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74537, d211373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74537, d211373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74538 q = 1) (hb : d211374 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74538, d211374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74538, d211374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74539 q = 1) (hb : d211375 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74539, d211375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74539, d211375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59752 (p : Pattern) (ha : d74545 p = 1) (hb : d211381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74540 q = 1) (hb : d211376 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74540, d211376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59751 q ha hb
    | true =>
      simp only [d74540, d211376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74541 q = 1) (hb : d211377 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74541, d211377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74541, d211377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74542 q = 1) (hb : d211378 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74542, d211378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74542, d211378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74543 q = 1) (hb : d211379 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74543, d211379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74543, d211379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74544 q = 1) (hb : d211380 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74544, d211380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74544, d211380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74545 q = 1) (hb : d211381 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74545, d211381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74545, d211381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59753 (p : Pattern) (ha : d74551 p = 1) (hb : d211387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74546 q = 1) (hb : d211382 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74546, d211382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59752 q ha hb
    | true =>
      simp only [d74546, d211382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74547 q = 1) (hb : d211383 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74547, d211383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74547, d211383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74548 q = 1) (hb : d211384 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74548, d211384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74548, d211384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74549 q = 1) (hb : d211385 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74549, d211385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74549, d211385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74550 q = 1) (hb : d211386 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74550, d211386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74550, d211386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74551 q = 1) (hb : d211387 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74551, d211387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74551, d211387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59754 (p : Pattern) (ha : d74557 p = 1) (hb : d211393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74552 q = 1) (hb : d211388 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74552, d211388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59753 q ha hb
    | true =>
      simp only [d74552, d211388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74553 q = 1) (hb : d211389 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74553, d211389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74553, d211389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74554 q = 1) (hb : d211390 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74554, d211390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74554, d211390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74555 q = 1) (hb : d211391 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74555, d211391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74555, d211391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74556 q = 1) (hb : d211392 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74556, d211392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74556, d211392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74557 q = 1) (hb : d211393 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74557, d211393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74557, d211393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59755 (p : Pattern) (ha : d74563 p = 1) (hb : d211399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74558 q = 1) (hb : d211394 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74558, d211394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59754 q ha hb
    | true =>
      simp only [d74558, d211394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74559 q = 1) (hb : d211395 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74559, d211395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74559, d211395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74560 q = 1) (hb : d211396 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74560, d211396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74560, d211396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74561 q = 1) (hb : d211397 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74561, d211397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74561, d211397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74562 q = 1) (hb : d211398 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74562, d211398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74562, d211398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74563 q = 1) (hb : d211399 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74563, d211399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74563, d211399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59756 (p : Pattern) (ha : d74569 p = 1) (hb : d211405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74564 q = 1) (hb : d211400 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74564, d211400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59755 q ha hb
    | true =>
      simp only [d74564, d211400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74565 q = 1) (hb : d211401 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74565, d211401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74565, d211401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74566 q = 1) (hb : d211402 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74566, d211402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74566, d211402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74567 q = 1) (hb : d211403 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74567, d211403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74567, d211403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74568 q = 1) (hb : d211404 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74568, d211404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74568, d211404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74569 q = 1) (hb : d211405 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74569, d211405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74569, d211405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59757 (p : Pattern) (ha : d74575 p = 1) (hb : d211411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74570 q = 1) (hb : d211406 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74570, d211406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59756 q ha hb
    | true =>
      simp only [d74570, d211406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74571 q = 1) (hb : d211407 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74571, d211407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74571, d211407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74572 q = 1) (hb : d211408 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74572, d211408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74572, d211408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74573 q = 1) (hb : d211409 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74573, d211409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74573, d211409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74574 q = 1) (hb : d211410 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74574, d211410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74574, d211410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74575 q = 1) (hb : d211411 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74575, d211411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74575, d211411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59758 (p : Pattern) (ha : d231166 p = 1) (hb : d231379 p = 1) : d231379 p = 1 := by
  have h0 (q : Pattern) (ha : d231166 q = 1) (hb : d231379 q = 1) : d231379 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro59759 (p : Pattern) (ha : d23205 p = 1) (hb : d74080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23147 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57772 q ha hb
    | true =>
      simp only [d23147, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d23201 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23201, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23202 q = 1) (hb : d74077 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23202, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23203 q = 1) (hb : d74078 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23203, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23204 q = 1) (hb : d74079 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23204, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23205 q = 1) (hb : d74080 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23205, d74080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23205, d74080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59760 (p : Pattern) (ha : d23212 p = 1) (hb : d74087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23147 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57772 q ha hb
    | true =>
      simp only [d23147, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d23201 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23201, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23202 q = 1) (hb : d74077 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23202, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23203 q = 1) (hb : d74078 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23203, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23204 q = 1) (hb : d74079 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d23154 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57774 q ha hb
    | true =>
      simp only [d23154, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d23208 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23208, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23209 q = 1) (hb : d74084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23209, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23210 q = 1) (hb : d74085 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d74085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23210, d74085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23211 q = 1) (hb : d74086 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d74086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23211, d74086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23212 q = 1) (hb : d74087 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23212, d74087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23212, d74087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59761 (p : Pattern) (ha : d74094 p = 1) (hb : d231169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23154 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57774 q ha hb
    | true =>
      simp only [d23154, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d23208 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23208, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23209 q = 1) (hb : d74084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23209, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23210 q = 1) (hb : d74092 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d74092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23210, d74092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23211 q = 1) (hb : d74093 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d74093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23211, d74093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74094 q = 1) (hb : d231169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74094, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74094, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59762 (p : Pattern) (ha : d74109 p = 1) (hb : d231179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52196 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23184 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23184, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57779 q ha hb
    | true =>
      simp only [d23184, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d52197 q = 1) (hb : d231175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52197, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52197, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74106 q = 1) (hb : d231176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74106, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74106, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74107 q = 1) (hb : d231177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74107, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74107, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74108 q = 1) (hb : d231178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74108, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74108, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74109 q = 1) (hb : d231179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74109, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74109, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59763 (p : Pattern) (ha : d74115 p = 1) (hb : d231185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23213 q = 1) (hb : d74088 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23213, d74088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59759 q ha hb
    | true =>
      simp only [d23213, d74088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59760 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23214 q = 1) (hb : d74089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23214, d74089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23214, d74089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74090 q = 1) (hb : d231167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74090, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74090, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74091 q = 1) (hb : d231168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74091, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74091, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74095 q = 1) (hb : d231170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74095, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74095, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59761 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74096 q = 1) (hb : d231171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74096, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74096, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74097 q = 1) (hb : d231172 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74097, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74097, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74098 q = 1) (hb : d231173 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74098, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74098, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74099 q = 1) (hb : d231174 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74099, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74099, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74110 q = 1) (hb : d231180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74110, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74110, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59762 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74111 q = 1) (hb : d231181 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74111, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74111, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74112 q = 1) (hb : d231182 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74112, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74112, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74113 q = 1) (hb : d231183 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74113, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74113, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74114 q = 1) (hb : d231184 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74114, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74114, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74115 q = 1) (hb : d231185 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74115, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74115, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59764 (p : Pattern) (ha : d74121 p = 1) (hb : d231191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52074 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro327 q ha hb
  have h3 (q : Pattern) (ha : d52075 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52076 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52077 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52078 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74116 q = 1) (hb : d231186 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74116, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74116, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59763 q ha hb
  have h8 (q : Pattern) (ha : d74117 q = 1) (hb : d231187 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74117, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74117, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74118 q = 1) (hb : d231188 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74118, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74118, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74119 q = 1) (hb : d231189 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74119, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74119, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74120 q = 1) (hb : d231190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74120, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74120, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74121 q = 1) (hb : d231191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74121, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74121, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro59765 (p : Pattern) (ha : d23388 p = 1) (hb : d74131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23383 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59526 q ha hb
    | true =>
      simp only [d23383, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57809 q ha hb
  have h5 (q : Pattern) (ha : d23384 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23384, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23385 q = 1) (hb : d74128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23385, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23386 q = 1) (hb : d74129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23386, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23387 q = 1) (hb : d74130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23387, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23388 q = 1) (hb : d74131 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23388, d74131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23388, d74131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59766 (p : Pattern) (ha : d23398 p = 1) (hb : d74138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23383 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59526 q ha hb
    | true =>
      simp only [d23383, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57809 q ha hb
  have h4 (q : Pattern) (ha : d23384 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23384, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23385 q = 1) (hb : d74128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23385, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23386 q = 1) (hb : d74129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23386, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23387 q = 1) (hb : d74130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d23393 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23393, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59528 q ha hb
    | true =>
      simp only [d23393, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57812 q ha hb
  have h13 (q : Pattern) (ha : d23394 q = 1) (hb : d52329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23394, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23395 q = 1) (hb : d74135 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23395, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23396 q = 1) (hb : d74136 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d74136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23396, d74136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23397 q = 1) (hb : d74137 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d74137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23397, d74137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23398 q = 1) (hb : d74138 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23398, d74138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23398, d74138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59767 (p : Pattern) (ha : d74145 p = 1) (hb : d231194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23393 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23393, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59528 q ha hb
    | true =>
      simp only [d23393, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57812 q ha hb
  have h3 (q : Pattern) (ha : d23394 q = 1) (hb : d52329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23394, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23395 q = 1) (hb : d74135 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23395, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23396 q = 1) (hb : d74143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d74143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23396, d74143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23397 q = 1) (hb : d74144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d74144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23397, d74144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74145 q = 1) (hb : d231194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74145, d231194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74145, d231194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59768 (p : Pattern) (ha : d74160 p = 1) (hb : d231205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52399 q = 1) (hb : d231200 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52399, d231200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59549 q hb ha
    | true =>
      simp only [d52399, d231200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57818 q hb ha
  have h3 (q : Pattern) (ha : d52400 q = 1) (hb : d231201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52400, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52400, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74157 q = 1) (hb : d231202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74157, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74157, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74158 q = 1) (hb : d231203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74158, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74158, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74159 q = 1) (hb : d231204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74159, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74159, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74160 q = 1) (hb : d231205 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74160, d231205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74160, d231205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59769 (p : Pattern) (ha : d74166 p = 1) (hb : d231211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23399 q = 1) (hb : d74139 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23399, d74139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59765 q ha hb
    | true =>
      simp only [d23399, d74139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59766 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23400 q = 1) (hb : d74140 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23400, d74140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23400, d74140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74141 q = 1) (hb : d231192 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74141, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74141, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74142 q = 1) (hb : d231193 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74142, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74142, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74146 q = 1) (hb : d231195 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74146, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74146, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59767 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74147 q = 1) (hb : d231196 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74147, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74147, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74148 q = 1) (hb : d231197 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74148, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74148, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74149 q = 1) (hb : d231198 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74149, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74149, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74150 q = 1) (hb : d231199 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74150, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74150, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74161 q = 1) (hb : d231206 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74161, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74161, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59768 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74162 q = 1) (hb : d231207 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74162, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74162, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74163 q = 1) (hb : d231208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74163, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74163, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74164 q = 1) (hb : d231209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74164, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74164, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74165 q = 1) (hb : d231210 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74165, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74165, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74166 q = 1) (hb : d231211 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74166, d231211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74166, d231211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59770 (p : Pattern) (ha : d74172 p = 1) (hb : d231217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74167 q = 1) (hb : d231212 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74167, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74167, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59769 q ha hb
  have h2 (q : Pattern) (ha : d74168 q = 1) (hb : d231213 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74168, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74168, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74169 q = 1) (hb : d231214 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74169, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74169, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74170 q = 1) (hb : d231215 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74170, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74170, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74171 q = 1) (hb : d231216 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74171, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74171, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74172 q = 1) (hb : d231217 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74172, d231217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74172, d231217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59771 (p : Pattern) (ha : d23661 p = 1) (hb : d74201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23656 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59556 q ha hb
    | true =>
      simp only [d23656, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57853 q ha hb
  have h5 (q : Pattern) (ha : d23657 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23657, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74197 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23658 q = 1) (hb : d74198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23658, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23659 q = 1) (hb : d74199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23659, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23660 q = 1) (hb : d74200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23660, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23661 q = 1) (hb : d74201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23661, d74201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23661, d74201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59772 (p : Pattern) (ha : d23671 p = 1) (hb : d74208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23656 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59556 q ha hb
    | true =>
      simp only [d23656, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57853 q ha hb
  have h4 (q : Pattern) (ha : d23657 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23657, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74197 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23658 q = 1) (hb : d74198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23658, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23659 q = 1) (hb : d74199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23659, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23660 q = 1) (hb : d74200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d23666 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23666, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59558 q ha hb
    | true =>
      simp only [d23666, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57856 q ha hb
  have h13 (q : Pattern) (ha : d23667 q = 1) (hb : d52550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23667, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74204 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23668 q = 1) (hb : d74205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23668, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23669 q = 1) (hb : d74206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d74206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23669, d74206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23670 q = 1) (hb : d74207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d74207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23670, d74207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23671 q = 1) (hb : d74208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23671, d74208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23671, d74208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59773 (p : Pattern) (ha : d74215 p = 1) (hb : d231221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23666 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23666, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59558 q ha hb
    | true =>
      simp only [d23666, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57856 q ha hb
  have h3 (q : Pattern) (ha : d23667 q = 1) (hb : d52550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23667, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74204 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23668 q = 1) (hb : d74205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23668, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23669 q = 1) (hb : d74213 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d74213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23669, d74213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23670 q = 1) (hb : d74214 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d74214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23670, d74214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74215 q = 1) (hb : d231221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74215, d231221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74215, d231221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59774 (p : Pattern) (ha : d74245 p = 1) (hb : d231232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52631 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52636 q = 1) (hb : d231227 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52636, d231227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59582 q hb ha
    | true =>
      simp only [d52636, d231227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57863 q hb ha
  have h3 (q : Pattern) (ha : d52637 q = 1) (hb : d231228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52637, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52637, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74241 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74242 q = 1) (hb : d231229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74242, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74242, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74243 q = 1) (hb : d231230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74243, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74243, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74244 q = 1) (hb : d231231 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74244, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74244, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74245 q = 1) (hb : d231232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74245, d231232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74245, d231232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59775 (p : Pattern) (ha : d74251 p = 1) (hb : d231238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23672 q = 1) (hb : d74209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23672, d74209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59771 q ha hb
    | true =>
      simp only [d23672, d74209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59772 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23673 q = 1) (hb : d74210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23673, d74210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23673, d74210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74211 q = 1) (hb : d231219 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74211, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74211, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74212 q = 1) (hb : d231220 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74212, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74212, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74216 q = 1) (hb : d231222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74216, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74216, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59773 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74217 q = 1) (hb : d231223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74217, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74217, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74218 q = 1) (hb : d231224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74218, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74218, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74219 q = 1) (hb : d231225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74219, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74219, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74220 q = 1) (hb : d231226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74220, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74220, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74246 q = 1) (hb : d231233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74246, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74246, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59774 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74247 q = 1) (hb : d231234 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74247, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74247, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74248 q = 1) (hb : d231235 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74248, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74248, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74249 q = 1) (hb : d231236 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74249, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74249, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74250 q = 1) (hb : d231237 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74250, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74250, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74251 q = 1) (hb : d231238 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74251, d231238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74251, d231238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59776 (p : Pattern) (ha : d74257 p = 1) (hb : d231244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74252 q = 1) (hb : d231239 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74252, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74252, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59775 q ha hb
  have h2 (q : Pattern) (ha : d74253 q = 1) (hb : d231240 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74253, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74253, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74254 q = 1) (hb : d231241 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74254, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74254, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74255 q = 1) (hb : d231242 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74255, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74255, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74256 q = 1) (hb : d231243 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74256, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74256, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74257 q = 1) (hb : d231244 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74257, d231244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74257, d231244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59777 (p : Pattern) (ha : d23983 p = 1) (hb : d74290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23978 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59597 q ha hb
    | true =>
      simp only [d23978, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59598 q ha hb
  have h5 (q : Pattern) (ha : d23979 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23979, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23980 q = 1) (hb : d74287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23980, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23981 q = 1) (hb : d74288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23981, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23982 q = 1) (hb : d74289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23982, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23983 q = 1) (hb : d74290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23983, d74290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23983, d74290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59778 (p : Pattern) (ha : d23993 p = 1) (hb : d74297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23978 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59597 q ha hb
    | true =>
      simp only [d23978, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59598 q ha hb
  have h4 (q : Pattern) (ha : d23979 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23979, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23980 q = 1) (hb : d74287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23980, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23981 q = 1) (hb : d74288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23981, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23982 q = 1) (hb : d74289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d23988 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23988, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59600 q ha hb
    | true =>
      simp only [d23988, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59601 q ha hb
  have h13 (q : Pattern) (ha : d23989 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23989, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23989, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23990 q = 1) (hb : d74294 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23990, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23991 q = 1) (hb : d74295 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d74295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23991, d74295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23992 q = 1) (hb : d74296 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d74296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23992, d74296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23993 q = 1) (hb : d74297 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23993, d74297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23993, d74297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59779 (p : Pattern) (ha : d74304 p = 1) (hb : d231249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23988 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23988, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59600 q ha hb
    | true =>
      simp only [d23988, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59601 q ha hb
  have h3 (q : Pattern) (ha : d23989 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23989, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23989, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23990 q = 1) (hb : d74294 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23990, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23991 q = 1) (hb : d74302 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d74302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23991, d74302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23992 q = 1) (hb : d74303 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d74303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23992, d74303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74304 q = 1) (hb : d231249 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74304, d231249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74304, d231249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59780 (p : Pattern) (ha : d74334 p = 1) (hb : d231260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52930 q = 1) (hb : d231255 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52930, d231255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59636 q hb ha
    | true =>
      simp only [d52930, d231255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59609 q hb ha
  have h3 (q : Pattern) (ha : d52931 q = 1) (hb : d231256 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52931, d231256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52931, d231256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74330 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74331 q = 1) (hb : d231257 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74331, d231257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74331, d231257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74332 q = 1) (hb : d231258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74332, d231258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74332, d231258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74333 q = 1) (hb : d231259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74333, d231259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74333, d231259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74334 q = 1) (hb : d231260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74334, d231260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74334, d231260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59781 (p : Pattern) (ha : d74340 p = 1) (hb : d231266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23994 q = 1) (hb : d74298 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23994, d74298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59777 q ha hb
    | true =>
      simp only [d23994, d74298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59778 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23995 q = 1) (hb : d74299 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23995, d74299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23995, d74299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74300 q = 1) (hb : d231247 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74300, d231247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74300, d231247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74301 q = 1) (hb : d231248 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74301, d231248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74301, d231248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74305 q = 1) (hb : d231250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74305, d231250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74305, d231250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59779 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74306 q = 1) (hb : d231251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74306, d231251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74306, d231251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74307 q = 1) (hb : d231252 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74307, d231252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74307, d231252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74308 q = 1) (hb : d231253 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74308, d231253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74308, d231253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74309 q = 1) (hb : d231254 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74309, d231254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74309, d231254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74335 q = 1) (hb : d231261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74335, d231261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74335, d231261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59780 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74336 q = 1) (hb : d231262 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74336, d231262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74336, d231262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74337 q = 1) (hb : d231263 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74337, d231263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74337, d231263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74338 q = 1) (hb : d231264 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74338, d231264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74338, d231264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74339 q = 1) (hb : d231265 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74339, d231265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74339, d231265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74340 q = 1) (hb : d231266 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74340, d231266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74340, d231266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59782 (p : Pattern) (ha : d74346 p = 1) (hb : d231272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74341 q = 1) (hb : d231267 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74341, d231267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74341, d231267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59781 q ha hb
  have h2 (q : Pattern) (ha : d74342 q = 1) (hb : d231268 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74342, d231268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74342, d231268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74343 q = 1) (hb : d231269 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74343, d231269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74343, d231269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74344 q = 1) (hb : d231270 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74344, d231270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74344, d231270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74345 q = 1) (hb : d231271 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74345, d231271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74345, d231271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74346 q = 1) (hb : d231272 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74346, d231272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74346, d231272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59783 (p : Pattern) (ha : d24365 p = 1) (hb : d74380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24360 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24360, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59651 q ha hb
    | true =>
      simp only [d24360, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59652 q ha hb
  have h5 (q : Pattern) (ha : d24361 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24361, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24361, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24362 q = 1) (hb : d74377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24362, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24363 q = 1) (hb : d74378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24363, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d24364 q = 1) (hb : d74379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24364, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24365 q = 1) (hb : d74380 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24365, d74380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24365, d74380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59784 (p : Pattern) (ha : d24375 p = 1) (hb : d74387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24360 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24360, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59651 q ha hb
    | true =>
      simp only [d24360, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59652 q ha hb
  have h4 (q : Pattern) (ha : d24361 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24361, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24361, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24362 q = 1) (hb : d74377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24362, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24363 q = 1) (hb : d74378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24363, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24364 q = 1) (hb : d74379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24364, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d24370 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24370, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59654 q ha hb
    | true =>
      simp only [d24370, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59655 q ha hb
  have h13 (q : Pattern) (ha : d24371 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24371, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24371, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d24372 q = 1) (hb : d74384 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24372, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d24373 q = 1) (hb : d74385 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d74385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24373, d74385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24374 q = 1) (hb : d74386 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d74386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24374, d74386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d24375 q = 1) (hb : d74387 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24375, d74387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24375, d74387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59785 (p : Pattern) (ha : d74394 p = 1) (hb : d231278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d24370 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24370, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59654 q ha hb
    | true =>
      simp only [d24370, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59655 q ha hb
  have h3 (q : Pattern) (ha : d24371 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24371, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24371, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d24372 q = 1) (hb : d74384 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24372, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24373 q = 1) (hb : d74392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d74392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24373, d74392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24374 q = 1) (hb : d74393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d74393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24374, d74393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74394 q = 1) (hb : d231278 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74394, d231278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74394, d231278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59786 (p : Pattern) (ha : d74424 p = 1) (hb : d231289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53240 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53245 q = 1) (hb : d231284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53245, d231284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59690 q hb ha
    | true =>
      simp only [d53245, d231284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59663 q hb ha
  have h3 (q : Pattern) (ha : d53246 q = 1) (hb : d231285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53246, d231285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53246, d231285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74420 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74421 q = 1) (hb : d231286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74421, d231286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74421, d231286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74422 q = 1) (hb : d231287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74422, d231287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74422, d231287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74423 q = 1) (hb : d231288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74423, d231288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74423, d231288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74424 q = 1) (hb : d231289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74424, d231289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74424, d231289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59787 (p : Pattern) (ha : d74430 p = 1) (hb : d231295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24376 q = 1) (hb : d74388 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24376, d74388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59783 q ha hb
    | true =>
      simp only [d24376, d74388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59784 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24377 q = 1) (hb : d74389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24377, d74389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24377, d74389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74390 q = 1) (hb : d231276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74390, d231276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74390, d231276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74391 q = 1) (hb : d231277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74391, d231277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74391, d231277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74395 q = 1) (hb : d231279 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74395, d231279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74395, d231279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59785 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74396 q = 1) (hb : d231280 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74396, d231280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74396, d231280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74397 q = 1) (hb : d231281 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74397, d231281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74397, d231281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74398 q = 1) (hb : d231282 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74398, d231282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74398, d231282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74399 q = 1) (hb : d231283 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74399, d231283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74399, d231283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74425 q = 1) (hb : d231290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74425, d231290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74425, d231290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59786 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74426 q = 1) (hb : d231291 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74426, d231291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74426, d231291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74427 q = 1) (hb : d231292 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74427, d231292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74427, d231292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74428 q = 1) (hb : d231293 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74428, d231293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74428, d231293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74429 q = 1) (hb : d231294 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74429, d231294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74429, d231294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74430 q = 1) (hb : d231295 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74430, d231295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74430, d231295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59788 (p : Pattern) (ha : d74436 p = 1) (hb : d231301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74431 q = 1) (hb : d231296 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74431, d231296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74431, d231296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59787 q ha hb
  have h2 (q : Pattern) (ha : d74432 q = 1) (hb : d231297 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74432, d231297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74432, d231297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74433 q = 1) (hb : d231298 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74433, d231298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74433, d231298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74434 q = 1) (hb : d231299 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74434, d231299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74434, d231299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74435 q = 1) (hb : d231300 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74435, d231300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74435, d231300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74436 q = 1) (hb : d231301 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74436, d231301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74436, d231301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59789 (p : Pattern) (ha : d24746 p = 1) (hb : d74471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24741 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24741, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59705 q ha hb
    | true =>
      simp only [d24741, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59706 q ha hb
  have h5 (q : Pattern) (ha : d24742 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24742, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24742, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24743 q = 1) (hb : d74468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24743, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24743, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24744 q = 1) (hb : d74469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24744, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24744, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d24745 q = 1) (hb : d74470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24745, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24745, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24746 q = 1) (hb : d74471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24746, d74471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24746, d74471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59790 (p : Pattern) (ha : d24756 p = 1) (hb : d74478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24741 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24741, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59705 q ha hb
    | true =>
      simp only [d24741, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59706 q ha hb
  have h4 (q : Pattern) (ha : d24742 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24742, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24742, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24743 q = 1) (hb : d74468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24743, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24743, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24744 q = 1) (hb : d74469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24744, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24744, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24745 q = 1) (hb : d74470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24745, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24745, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d24751 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24751, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59708 q ha hb
    | true =>
      simp only [d24751, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59709 q ha hb
  have h13 (q : Pattern) (ha : d24752 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24752, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24752, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d24753 q = 1) (hb : d74475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24753, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d24754 q = 1) (hb : d74476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d74476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24754, d74476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24755 q = 1) (hb : d74477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d74477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24755, d74477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d24756 q = 1) (hb : d74478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24756, d74478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24756, d74478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59791 (p : Pattern) (ha : d74485 p = 1) (hb : d231308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d24751 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24751, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59708 q ha hb
    | true =>
      simp only [d24751, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59709 q ha hb
  have h3 (q : Pattern) (ha : d24752 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24752, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24752, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d24753 q = 1) (hb : d74475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24753, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24754 q = 1) (hb : d74483 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d74483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24754, d74483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24755 q = 1) (hb : d74484 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d74484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24755, d74484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74485 q = 1) (hb : d231308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74485, d231308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74485, d231308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59792 (p : Pattern) (ha : d74515 p = 1) (hb : d231319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53562 q = 1) (hb : d231314 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53562, d231314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59743 q hb ha
    | true =>
      simp only [d53562, d231314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59717 q hb ha
  have h3 (q : Pattern) (ha : d53563 q = 1) (hb : d231315 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53563, d231315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53563, d231315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74511 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74512 q = 1) (hb : d231316 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74512, d231316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74512, d231316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74513 q = 1) (hb : d231317 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74513, d231317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74513, d231317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74514 q = 1) (hb : d231318 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74514, d231318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74514, d231318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74515 q = 1) (hb : d231319 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74515, d231319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74515, d231319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59793 (p : Pattern) (ha : d74521 p = 1) (hb : d231325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24757 q = 1) (hb : d74479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24757, d74479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59789 q ha hb
    | true =>
      simp only [d24757, d74479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59790 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24758 q = 1) (hb : d74480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24758, d74480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24758, d74480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74481 q = 1) (hb : d231306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74481, d231306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74481, d231306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74482 q = 1) (hb : d231307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74482, d231307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74482, d231307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74486 q = 1) (hb : d231309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74486, d231309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74486, d231309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59791 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74487 q = 1) (hb : d231310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74487, d231310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74487, d231310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74488 q = 1) (hb : d231311 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74488, d231311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74488, d231311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74489 q = 1) (hb : d231312 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74489, d231312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74489, d231312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74490 q = 1) (hb : d231313 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74490, d231313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74490, d231313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74516 q = 1) (hb : d231320 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74516, d231320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74516, d231320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59792 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74517 q = 1) (hb : d231321 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74517, d231321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74517, d231321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74518 q = 1) (hb : d231322 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74518, d231322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74518, d231322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74519 q = 1) (hb : d231323 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74519, d231323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74519, d231323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74520 q = 1) (hb : d231324 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74520, d231324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74520, d231324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74521 q = 1) (hb : d231325 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74521, d231325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74521, d231325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59794 (p : Pattern) (ha : d74527 p = 1) (hb : d231331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74522 q = 1) (hb : d231326 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74522, d231326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74522, d231326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59793 q ha hb
  have h2 (q : Pattern) (ha : d74523 q = 1) (hb : d231327 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74523, d231327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74523, d231327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74524 q = 1) (hb : d231328 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74524, d231328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74524, d231328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74525 q = 1) (hb : d231329 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74525, d231329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74525, d231329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74526 q = 1) (hb : d231330 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74526, d231330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74526, d231330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74527 q = 1) (hb : d231331 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74527, d231331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74527, d231331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59795 (p : Pattern) (ha : d74533 p = 1) (hb : d231337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d74173 q = 1) (hb : d231218 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74173, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59764 q ha hb
    | true =>
      simp only [d74173, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59770 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74258 q = 1) (hb : d231245 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74258, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74258, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59776 q ha hb
  have h3 (q : Pattern) (ha : d74259 q = 1) (hb : d231246 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74259, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74259, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74347 q = 1) (hb : d231273 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74347, d231273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74347, d231273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59782 q ha hb
  have h5 (q : Pattern) (ha : d74348 q = 1) (hb : d231274 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74348, d231274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74348, d231274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74349 q = 1) (hb : d231275 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74349, d231275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74349, d231275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74437 q = 1) (hb : d231302 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74437, d231302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74437, d231302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59788 q ha hb
  have h8 (q : Pattern) (ha : d74438 q = 1) (hb : d231303 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74438, d231303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74438, d231303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74439 q = 1) (hb : d231304 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74439, d231304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74439, d231304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74440 q = 1) (hb : d231305 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74440, d231305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74440, d231305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74528 q = 1) (hb : d231332 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74528, d231332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74528, d231332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59794 q ha hb
  have h12 (q : Pattern) (ha : d74529 q = 1) (hb : d231333 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74529, d231333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74529, d231333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74530 q = 1) (hb : d231334 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74530, d231334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74530, d231334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74531 q = 1) (hb : d231335 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74531, d231335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74531, d231335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74532 q = 1) (hb : d231336 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74532, d231336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74532, d231336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74533 q = 1) (hb : d231337 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74533, d231337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74533, d231337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro59796 (p : Pattern) (ha : d74539 p = 1) (hb : d231343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74534 q = 1) (hb : d231338 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74534, d231338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59795 q ha hb
    | true =>
      simp only [d74534, d231338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74535 q = 1) (hb : d231339 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74535, d231339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74535, d231339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74536 q = 1) (hb : d231340 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74536, d231340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74536, d231340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74537 q = 1) (hb : d231341 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74537, d231341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74537, d231341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74538 q = 1) (hb : d231342 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74538, d231342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74538, d231342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74539 q = 1) (hb : d231343 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74539, d231343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74539, d231343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59797 (p : Pattern) (ha : d74545 p = 1) (hb : d231349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74540 q = 1) (hb : d231344 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74540, d231344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59796 q ha hb
    | true =>
      simp only [d74540, d231344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74541 q = 1) (hb : d231345 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74541, d231345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74541, d231345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74542 q = 1) (hb : d231346 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74542, d231346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74542, d231346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74543 q = 1) (hb : d231347 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74543, d231347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74543, d231347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74544 q = 1) (hb : d231348 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74544, d231348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74544, d231348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74545 q = 1) (hb : d231349 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74545, d231349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74545, d231349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59798 (p : Pattern) (ha : d74551 p = 1) (hb : d231355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74546 q = 1) (hb : d231350 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74546, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59797 q ha hb
    | true =>
      simp only [d74546, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74547 q = 1) (hb : d231351 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74547, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74547, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74548 q = 1) (hb : d231352 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74548, d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74548, d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74549 q = 1) (hb : d231353 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74549, d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74549, d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74550 q = 1) (hb : d231354 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74550, d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74550, d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74551 q = 1) (hb : d231355 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74551, d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74551, d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59799 (p : Pattern) (ha : d74557 p = 1) (hb : d231361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74552 q = 1) (hb : d231356 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74552, d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59798 q ha hb
    | true =>
      simp only [d74552, d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74553 q = 1) (hb : d231357 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74553, d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74553, d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74554 q = 1) (hb : d231358 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74554, d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74554, d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74555 q = 1) (hb : d231359 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74555, d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74555, d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74556 q = 1) (hb : d231360 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74556, d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74556, d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74557 q = 1) (hb : d231361 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74557, d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74557, d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59800 (p : Pattern) (ha : d74563 p = 1) (hb : d231367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74558 q = 1) (hb : d231362 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74558, d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59799 q ha hb
    | true =>
      simp only [d74558, d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74559 q = 1) (hb : d231363 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74559, d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74559, d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74560 q = 1) (hb : d231364 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74560, d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74560, d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74561 q = 1) (hb : d231365 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74561, d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74561, d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74562 q = 1) (hb : d231366 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74562, d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74562, d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74563 q = 1) (hb : d231367 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74563, d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74563, d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59801 (p : Pattern) (ha : d74569 p = 1) (hb : d231373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74564 q = 1) (hb : d231368 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74564, d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59800 q ha hb
    | true =>
      simp only [d74564, d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74565 q = 1) (hb : d231369 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74565, d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74565, d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74566 q = 1) (hb : d231370 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74566, d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74566, d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74567 q = 1) (hb : d231371 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74567, d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74567, d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74568 q = 1) (hb : d231372 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74568, d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74568, d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74569 q = 1) (hb : d231373 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74569, d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74569, d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59802 (p : Pattern) (ha : d74575 p = 1) (hb : d231379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74570 q = 1) (hb : d231374 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74570, d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59801 q ha hb
    | true =>
      simp only [d74570, d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74571 q = 1) (hb : d231375 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74571, d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74571, d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74572 q = 1) (hb : d231376 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74572, d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74572, d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74573 q = 1) (hb : d231377 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74573, d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74573, d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74574 q = 1) (hb : d231378 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74574, d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74574, d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74575 q = 1) (hb : d231379 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74575, d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74575, d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59803 (p : Pattern) (ha : d23205 p = 1) (hb : d74579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4371 q = 1) (hb : d23201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4371, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23202 q = 1) (hb : d74576 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d23202, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23203 q = 1) (hb : d74577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23203, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23204 q = 1) (hb : d74578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23204, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23205 q = 1) (hb : d74579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23205, d74579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23205, d74579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59804 (p : Pattern) (ha : d23212 p = 1) (hb : d74583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23147 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4371 q = 1) (hb : d23201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4371, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23202 q = 1) (hb : d74576 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d23202, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23203 q = 1) (hb : d74577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23203, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23204 q = 1) (hb : d74578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d386 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d23154 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4376 q = 1) (hb : d23208 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4376, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23209 q = 1) (hb : d74580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d23209, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23210 q = 1) (hb : d74581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d74581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23210, d74581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23211 q = 1) (hb : d74582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d74582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23211, d74582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23212 q = 1) (hb : d74583 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23212, d74583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23212, d74583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59805 (p : Pattern) (ha : d74590 p = 1) (hb : d231169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4376 q = 1) (hb : d23208 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4376, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23209 q = 1) (hb : d74580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d23209, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23210 q = 1) (hb : d74588 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d74588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23210, d74588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23211 q = 1) (hb : d74589 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d74589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23211, d74589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74590 q = 1) (hb : d231169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74590, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74590, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59806 (p : Pattern) (ha : d74599 p = 1) (hb : d231179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d430 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23184 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4391 q = 1) (hb : d231175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4391, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74596 q = 1) (hb : d231176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74596, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74596, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74597 q = 1) (hb : d231177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74597, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74597, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74598 q = 1) (hb : d231178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74598, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74598, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74599 q = 1) (hb : d231179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74599, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74599, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59807 (p : Pattern) (ha : d74605 p = 1) (hb : d231185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23213 q = 1) (hb : d74584 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23213, d74584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59803 q ha hb
    | true =>
      simp only [d23213, d74584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59804 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23214 q = 1) (hb : d74585 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23214, d74585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23214, d74585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74586 q = 1) (hb : d231167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74586, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74586, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74587 q = 1) (hb : d231168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74587, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74587, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74591 q = 1) (hb : d231170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74591, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74591, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59805 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74592 q = 1) (hb : d231171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74592, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74592, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74593 q = 1) (hb : d231172 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74593, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74593, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74594 q = 1) (hb : d231173 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74594, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74594, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74595 q = 1) (hb : d231174 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74595, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74595, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74600 q = 1) (hb : d231180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74600, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74600, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59806 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74601 q = 1) (hb : d231181 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74601, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74601, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74602 q = 1) (hb : d231182 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74602, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74602, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74603 q = 1) (hb : d231183 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74603, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74603, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74604 q = 1) (hb : d231184 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74604, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74604, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74605 q = 1) (hb : d231185 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74605, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74605, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59808 (p : Pattern) (ha : d74611 p = 1) (hb : d231191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro376 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74606 q = 1) (hb : d231186 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74606, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74606, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59807 q ha hb
  have h8 (q : Pattern) (ha : d74607 q = 1) (hb : d231187 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74607, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74607, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74608 q = 1) (hb : d231188 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74608, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74608, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74609 q = 1) (hb : d231189 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74609, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74609, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74610 q = 1) (hb : d231190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74610, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74610, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74611 q = 1) (hb : d231191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74611, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74611, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro59809 (p : Pattern) (ha : d23388 p = 1) (hb : d74615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d561 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23383 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4408 q = 1) (hb : d23384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4408, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23385 q = 1) (hb : d74612 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d74612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d23385, d74612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23386 q = 1) (hb : d74613 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d74613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23386, d74613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23387 q = 1) (hb : d74614 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d74614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23387, d74614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23388 q = 1) (hb : d74615 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23388, d74615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23388, d74615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59810 (p : Pattern) (ha : d23398 p = 1) (hb : d74619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23383 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4408 q = 1) (hb : d23384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4408, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23385 q = 1) (hb : d74612 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d74612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d23385, d74612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23386 q = 1) (hb : d74613 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d74613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23386, d74613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23387 q = 1) (hb : d74614 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d74614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d74614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d614 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d619 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d621 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d23393 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4413 q = 1) (hb : d23394 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4413, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23395 q = 1) (hb : d74616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d74616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d23395, d74616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23396 q = 1) (hb : d74617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d74617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23396, d74617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23397 q = 1) (hb : d74618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d74618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23397, d74618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23398 q = 1) (hb : d74619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23398, d74619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23398, d74619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59811 (p : Pattern) (ha : d74626 p = 1) (hb : d231194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23393 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4413 q = 1) (hb : d23394 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4413, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23395 q = 1) (hb : d74616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d74616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d23395, d74616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23396 q = 1) (hb : d74624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d74624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23396, d74624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23397 q = 1) (hb : d74625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d74625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23397, d74625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74626 q = 1) (hb : d231194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74626, d231194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74626, d231194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59812 (p : Pattern) (ha : d74635 p = 1) (hb : d231205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231200 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4428 q = 1) (hb : d231201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4428, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5430 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74632 q = 1) (hb : d231202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74632, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74632, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74633 q = 1) (hb : d231203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74633, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74633, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74634 q = 1) (hb : d231204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74634, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74634, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74635 q = 1) (hb : d231205 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74635, d231205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74635, d231205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59813 (p : Pattern) (ha : d74641 p = 1) (hb : d231211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23399 q = 1) (hb : d74620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23399, d74620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59809 q ha hb
    | true =>
      simp only [d23399, d74620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59810 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d645 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23400 q = 1) (hb : d74621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23400, d74621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23400, d74621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74622 q = 1) (hb : d231192 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74622, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74622, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74623 q = 1) (hb : d231193 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74623, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74623, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74627 q = 1) (hb : d231195 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74627, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74627, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59811 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74628 q = 1) (hb : d231196 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74628, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74628, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74629 q = 1) (hb : d231197 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74629, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74629, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74630 q = 1) (hb : d231198 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74630, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74630, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74631 q = 1) (hb : d231199 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74631, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74631, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74636 q = 1) (hb : d231206 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74636, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74636, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59812 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74637 q = 1) (hb : d231207 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74637, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74637, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74638 q = 1) (hb : d231208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74638, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74638, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74639 q = 1) (hb : d231209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74639, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74639, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74640 q = 1) (hb : d231210 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74640, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74640, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74641 q = 1) (hb : d231211 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74641, d231211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74641, d231211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59814 (p : Pattern) (ha : d74647 p = 1) (hb : d231217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74642 q = 1) (hb : d231212 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74642, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74642, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59813 q ha hb
  have h2 (q : Pattern) (ha : d74643 q = 1) (hb : d231213 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74643, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74643, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74644 q = 1) (hb : d231214 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74644, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74644, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74645 q = 1) (hb : d231215 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74645, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74645, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74646 q = 1) (hb : d231216 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74646, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74646, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74647 q = 1) (hb : d231217 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74647, d231217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74647, d231217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59815 (p : Pattern) (ha : d23661 p = 1) (hb : d74652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23656 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4446 q = 1) (hb : d23657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4446, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5471 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23658 q = 1) (hb : d74649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d74649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d23658, d74649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23659 q = 1) (hb : d74650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d74650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23659, d74650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23660 q = 1) (hb : d74651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d74651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23660, d74651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23661 q = 1) (hb : d74652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23661, d74652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23661, d74652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59816 (p : Pattern) (ha : d23671 p = 1) (hb : d74656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d852 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23656 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4446 q = 1) (hb : d23657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4446, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5471 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23658 q = 1) (hb : d74649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d74649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d23658, d74649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23659 q = 1) (hb : d74650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d74650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23659, d74650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23660 q = 1) (hb : d74651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d74651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d74651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d920 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d925 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d927 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d23666 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4451 q = 1) (hb : d23667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4451, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5478 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23668 q = 1) (hb : d74653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d74653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d23668, d74653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23669 q = 1) (hb : d74654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d74654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23669, d74654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23670 q = 1) (hb : d74655 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d74655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23670, d74655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23671 q = 1) (hb : d74656 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23671, d74656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23671, d74656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59817 (p : Pattern) (ha : d74663 p = 1) (hb : d231221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d927 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23666 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4451 q = 1) (hb : d23667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4451, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5478 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23668 q = 1) (hb : d74653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d74653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d23668, d74653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23669 q = 1) (hb : d74661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d74661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23669, d74661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23670 q = 1) (hb : d74662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d74662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23670, d74662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74663 q = 1) (hb : d231221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74663, d231221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74663, d231221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59818 (p : Pattern) (ha : d74672 p = 1) (hb : d231232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1012 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4466 q = 1) (hb : d231228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4466, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5515 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74669 q = 1) (hb : d231229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74669, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74669, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74670 q = 1) (hb : d231230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74670, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74670, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74671 q = 1) (hb : d231231 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74671, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74671, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74672 q = 1) (hb : d231232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74672, d231232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74672, d231232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59819 (p : Pattern) (ha : d74678 p = 1) (hb : d231238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23672 q = 1) (hb : d74657 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23672, d74657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59815 q ha hb
    | true =>
      simp only [d23672, d74657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59816 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d951 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23673 q = 1) (hb : d74658 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23673, d74658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23673, d74658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74659 q = 1) (hb : d231219 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74659, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74659, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74660 q = 1) (hb : d231220 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74660, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74660, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74664 q = 1) (hb : d231222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74664, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74664, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59817 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74665 q = 1) (hb : d231223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74665, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74665, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74666 q = 1) (hb : d231224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74666, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74666, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74667 q = 1) (hb : d231225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74667, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74667, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74668 q = 1) (hb : d231226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74668, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74668, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74673 q = 1) (hb : d231233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74673, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74673, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59818 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74674 q = 1) (hb : d231234 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74674, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74674, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74675 q = 1) (hb : d231235 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74675, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74675, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74676 q = 1) (hb : d231236 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74676, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74676, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74677 q = 1) (hb : d231237 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74677, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74677, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74678 q = 1) (hb : d231238 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74678, d231238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74678, d231238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59820 (p : Pattern) (ha : d74684 p = 1) (hb : d231244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74679 q = 1) (hb : d231239 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74679, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74679, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59819 q ha hb
  have h2 (q : Pattern) (ha : d74680 q = 1) (hb : d231240 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74680, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74680, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74681 q = 1) (hb : d231241 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74681, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74681, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74682 q = 1) (hb : d231242 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74682, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74682, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74683 q = 1) (hb : d231243 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74683, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74683, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74684 q = 1) (hb : d231244 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74684, d231244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74684, d231244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59821 (p : Pattern) (ha : d23983 p = 1) (hb : d74690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23978 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4485 q = 1) (hb : d23979 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d23979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4485, d23979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5560 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23980 q = 1) (hb : d74687 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d74687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d23980, d74687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23981 q = 1) (hb : d74688 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d74688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23981, d74688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23982 q = 1) (hb : d74689 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d74689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23982, d74689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23983 q = 1) (hb : d74690 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23983, d74690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23983, d74690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59822 (p : Pattern) (ha : d23993 p = 1) (hb : d74694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23978 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4485 q = 1) (hb : d23979 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d23979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4485, d23979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5560 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23980 q = 1) (hb : d74687 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d74687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d23980, d74687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23981 q = 1) (hb : d74688 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d74688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23981, d74688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23982 q = 1) (hb : d74689 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d74689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d74689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1331 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1336 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1338 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d23988 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4490 q = 1) (hb : d23989 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d23989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4490, d23989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5567 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23990 q = 1) (hb : d74691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d74691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d23990, d74691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23991 q = 1) (hb : d74692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d74692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23991, d74692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23992 q = 1) (hb : d74693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d74693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23992, d74693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23993 q = 1) (hb : d74694 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23993, d74694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23993, d74694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59823 (p : Pattern) (ha : d74701 p = 1) (hb : d231249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4490 q = 1) (hb : d23989 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d23989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4490, d23989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5567 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23990 q = 1) (hb : d74691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d74691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d23990, d74691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23991 q = 1) (hb : d74699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d74699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23991, d74699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23992 q = 1) (hb : d74700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d74700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23992, d74700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74701 q = 1) (hb : d231249 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74701, d231249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74701, d231249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59824 (p : Pattern) (ha : d74710 p = 1) (hb : d231260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231255 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4505 q = 1) (hb : d231256 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d231256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4505, d231256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5604 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74707 q = 1) (hb : d231257 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74707, d231257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74707, d231257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74708 q = 1) (hb : d231258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74708, d231258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74708, d231258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74709 q = 1) (hb : d231259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74709, d231259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74709, d231259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74710 q = 1) (hb : d231260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74710, d231260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74710, d231260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59825 (p : Pattern) (ha : d74716 p = 1) (hb : d231266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23994 q = 1) (hb : d74695 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23994, d74695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59821 q ha hb
    | true =>
      simp only [d23994, d74695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59822 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23995 q = 1) (hb : d74696 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23995, d74696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23995, d74696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74697 q = 1) (hb : d231247 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74697, d231247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74697, d231247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74698 q = 1) (hb : d231248 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74698, d231248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74698, d231248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74702 q = 1) (hb : d231250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74702, d231250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74702, d231250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59823 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74703 q = 1) (hb : d231251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74703, d231251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74703, d231251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74704 q = 1) (hb : d231252 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74704, d231252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74704, d231252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74705 q = 1) (hb : d231253 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74705, d231253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74705, d231253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74706 q = 1) (hb : d231254 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74706, d231254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74706, d231254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74711 q = 1) (hb : d231261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74711, d231261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74711, d231261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59824 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74712 q = 1) (hb : d231262 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74712, d231262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74712, d231262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74713 q = 1) (hb : d231263 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74713, d231263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74713, d231263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74714 q = 1) (hb : d231264 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74714, d231264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74714, d231264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74715 q = 1) (hb : d231265 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74715, d231265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74715, d231265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74716 q = 1) (hb : d231266 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74716, d231266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74716, d231266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59826 (p : Pattern) (ha : d74722 p = 1) (hb : d231272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74717 q = 1) (hb : d231267 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74717, d231267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74717, d231267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59825 q ha hb
  have h2 (q : Pattern) (ha : d74718 q = 1) (hb : d231268 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74718, d231268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74718, d231268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74719 q = 1) (hb : d231269 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74719, d231269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74719, d231269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74720 q = 1) (hb : d231270 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74720, d231270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74720, d231270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74721 q = 1) (hb : d231271 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74721, d231271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74721, d231271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74722 q = 1) (hb : d231272 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74722, d231272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74722, d231272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59827 (p : Pattern) (ha : d24365 p = 1) (hb : d74729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24360 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4525 q = 1) (hb : d24361 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d24361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4525, d24361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5650 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24362 q = 1) (hb : d74726 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d74726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d24362, d74726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24363 q = 1) (hb : d74727 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d74727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24363, d74727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d24364 q = 1) (hb : d74728 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d74728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24364, d74728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24365 q = 1) (hb : d74729 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24365, d74729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24365, d74729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59828 (p : Pattern) (ha : d24375 p = 1) (hb : d74733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24360 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4525 q = 1) (hb : d24361 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d24361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4525, d24361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5650 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24362 q = 1) (hb : d74726 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d74726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d24362, d74726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24363 q = 1) (hb : d74727 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d74727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24363, d74727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24364 q = 1) (hb : d74728 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d74728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24364, d74728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1815 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d24370 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4530 q = 1) (hb : d24371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d24371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4530, d24371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5657 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d24372 q = 1) (hb : d74730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d74730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d24372, d74730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d24373 q = 1) (hb : d74731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d74731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24373, d74731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24374 q = 1) (hb : d74732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d74732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24374, d74732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d24375 q = 1) (hb : d74733 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24375, d74733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24375, d74733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59829 (p : Pattern) (ha : d74740 p = 1) (hb : d231278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24370 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4530 q = 1) (hb : d24371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d24371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4530, d24371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5657 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d24372 q = 1) (hb : d74730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d74730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d24372, d74730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24373 q = 1) (hb : d74738 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d74738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24373, d74738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24374 q = 1) (hb : d74739 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d74739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24374, d74739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74740 q = 1) (hb : d231278 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74740, d231278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74740, d231278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59830 (p : Pattern) (ha : d74749 p = 1) (hb : d231289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1914 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4545 q = 1) (hb : d231285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d231285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4545, d231285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5694 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74746 q = 1) (hb : d231286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74746, d231286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74746, d231286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74747 q = 1) (hb : d231287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74747, d231287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74747, d231287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74748 q = 1) (hb : d231288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74748, d231288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74748, d231288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74749 q = 1) (hb : d231289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74749, d231289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74749, d231289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59831 (p : Pattern) (ha : d74755 p = 1) (hb : d231295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24376 q = 1) (hb : d74734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24376, d74734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59827 q ha hb
    | true =>
      simp only [d24376, d74734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59828 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1839 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24377 q = 1) (hb : d74735 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24377, d74735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24377, d74735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74736 q = 1) (hb : d231276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74736, d231276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74736, d231276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74737 q = 1) (hb : d231277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74737, d231277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74737, d231277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74741 q = 1) (hb : d231279 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74741, d231279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74741, d231279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59829 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74742 q = 1) (hb : d231280 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74742, d231280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74742, d231280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74743 q = 1) (hb : d231281 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74743, d231281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74743, d231281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74744 q = 1) (hb : d231282 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74744, d231282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74744, d231282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74745 q = 1) (hb : d231283 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74745, d231283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74745, d231283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74750 q = 1) (hb : d231290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74750, d231290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74750, d231290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59830 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74751 q = 1) (hb : d231291 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74751, d231291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74751, d231291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74752 q = 1) (hb : d231292 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74752, d231292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74752, d231292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74753 q = 1) (hb : d231293 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74753, d231293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74753, d231293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74754 q = 1) (hb : d231294 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74754, d231294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74754, d231294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74755 q = 1) (hb : d231295 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74755, d231295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74755, d231295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59832 (p : Pattern) (ha : d74761 p = 1) (hb : d231301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74756 q = 1) (hb : d231296 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74756, d231296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74756, d231296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59831 q ha hb
  have h2 (q : Pattern) (ha : d74757 q = 1) (hb : d231297 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74757, d231297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74757, d231297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74758 q = 1) (hb : d231298 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74758, d231298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74758, d231298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74759 q = 1) (hb : d231299 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74759, d231299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74759, d231299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74760 q = 1) (hb : d231300 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74760, d231300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74760, d231300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74761 q = 1) (hb : d231301 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74761, d231301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74761, d231301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59833 (p : Pattern) (ha : d24746 p = 1) (hb : d74769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24741 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4566 q = 1) (hb : d24742 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d24742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4566, d24742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5741 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24743 q = 1) (hb : d74766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24743, d74766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d24743, d74766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24744 q = 1) (hb : d74767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24744, d74767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24744, d74767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d24745 q = 1) (hb : d74768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24745, d74768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24745, d74768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24746 q = 1) (hb : d74769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24746, d74769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24746, d74769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59834 (p : Pattern) (ha : d24756 p = 1) (hb : d74773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24741 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4566 q = 1) (hb : d24742 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d24742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4566, d24742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5741 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24743 q = 1) (hb : d74766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24743, d74766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d24743, d74766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24744 q = 1) (hb : d74767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24744, d74767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24744, d74767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24745 q = 1) (hb : d74768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24745, d74768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24745, d74768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2286 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2291 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d2293 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d24751 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4571 q = 1) (hb : d24752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d24752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4571, d24752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5748 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d24753 q = 1) (hb : d74770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d74770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d24753, d74770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d24754 q = 1) (hb : d74771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d74771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24754, d74771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24755 q = 1) (hb : d74772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d74772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24755, d74772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d24756 q = 1) (hb : d74773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24756, d74773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24756, d74773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59835 (p : Pattern) (ha : d74780 p = 1) (hb : d231308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2293 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24751 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4571 q = 1) (hb : d24752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d24752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4571, d24752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5748 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d24753 q = 1) (hb : d74770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d74770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d24753, d74770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24754 q = 1) (hb : d74778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d74778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24754, d74778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24755 q = 1) (hb : d74779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d74779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24755, d74779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74780 q = 1) (hb : d231308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74780, d231308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74780, d231308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59836 (p : Pattern) (ha : d74789 p = 1) (hb : d231319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231314 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4586 q = 1) (hb : d231315 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d231315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4586, d231315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5785 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74786 q = 1) (hb : d231316 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74786, d231316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74786, d231316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74787 q = 1) (hb : d231317 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74787, d231317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74787, d231317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74788 q = 1) (hb : d231318 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74788, d231318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74788, d231318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74789 q = 1) (hb : d231319 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74789, d231319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74789, d231319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59837 (p : Pattern) (ha : d74795 p = 1) (hb : d231325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24757 q = 1) (hb : d74774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24757, d74774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59833 q ha hb
    | true =>
      simp only [d24757, d74774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59834 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2317 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24758 q = 1) (hb : d74775 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24758, d74775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24758, d74775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74776 q = 1) (hb : d231306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74776, d231306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74776, d231306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74777 q = 1) (hb : d231307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74777, d231307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74777, d231307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74781 q = 1) (hb : d231309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74781, d231309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74781, d231309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59835 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74782 q = 1) (hb : d231310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74782, d231310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74782, d231310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74783 q = 1) (hb : d231311 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74783, d231311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74783, d231311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74784 q = 1) (hb : d231312 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74784, d231312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74784, d231312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74785 q = 1) (hb : d231313 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74785, d231313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74785, d231313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74790 q = 1) (hb : d231320 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74790, d231320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74790, d231320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59836 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74791 q = 1) (hb : d231321 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74791, d231321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74791, d231321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74792 q = 1) (hb : d231322 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74792, d231322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74792, d231322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74793 q = 1) (hb : d231323 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74793, d231323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74793, d231323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74794 q = 1) (hb : d231324 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74794, d231324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74794, d231324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74795 q = 1) (hb : d231325 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74795, d231325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74795, d231325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59838 (p : Pattern) (ha : d74801 p = 1) (hb : d231331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74796 q = 1) (hb : d231326 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74796, d231326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74796, d231326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59837 q ha hb
  have h2 (q : Pattern) (ha : d74797 q = 1) (hb : d231327 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74797, d231327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74797, d231327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74798 q = 1) (hb : d231328 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74798, d231328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74798, d231328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74799 q = 1) (hb : d231329 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74799, d231329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74799, d231329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74800 q = 1) (hb : d231330 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74800, d231330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74800, d231330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74801 q = 1) (hb : d231331 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74801, d231331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74801, d231331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59839 (p : Pattern) (ha : d74807 p = 1) (hb : d231337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d74648 q = 1) (hb : d231218 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74648, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59808 q ha hb
    | true =>
      simp only [d74648, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59814 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74685 q = 1) (hb : d231245 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74685, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74685, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59820 q ha hb
  have h3 (q : Pattern) (ha : d74686 q = 1) (hb : d231246 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74686, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74686, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74723 q = 1) (hb : d231273 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74723, d231273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74723, d231273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59826 q ha hb
  have h5 (q : Pattern) (ha : d74724 q = 1) (hb : d231274 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74724, d231274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74724, d231274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74725 q = 1) (hb : d231275 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74725, d231275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74725, d231275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74762 q = 1) (hb : d231302 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74762, d231302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74762, d231302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59832 q ha hb
  have h8 (q : Pattern) (ha : d74763 q = 1) (hb : d231303 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74763, d231303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74763, d231303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74764 q = 1) (hb : d231304 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74764, d231304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74764, d231304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74765 q = 1) (hb : d231305 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74765, d231305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74765, d231305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74802 q = 1) (hb : d231332 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74802, d231332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74802, d231332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59838 q ha hb
  have h12 (q : Pattern) (ha : d74803 q = 1) (hb : d231333 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74803, d231333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74803, d231333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74804 q = 1) (hb : d231334 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74804, d231334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74804, d231334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74805 q = 1) (hb : d231335 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74805, d231335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74805, d231335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74806 q = 1) (hb : d231336 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74806, d231336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74806, d231336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74807 q = 1) (hb : d231337 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74807, d231337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74807, d231337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro59840 (p : Pattern) (ha : d74813 p = 1) (hb : d231343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74808 q = 1) (hb : d231338 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74808, d231338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59839 q ha hb
    | true =>
      simp only [d74808, d231338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74809 q = 1) (hb : d231339 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74809, d231339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74809, d231339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74810 q = 1) (hb : d231340 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74810, d231340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74810, d231340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74811 q = 1) (hb : d231341 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74811, d231341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74811, d231341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74812 q = 1) (hb : d231342 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74812, d231342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74812, d231342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74813 q = 1) (hb : d231343 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74813, d231343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74813, d231343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59841 (p : Pattern) (ha : d74819 p = 1) (hb : d231349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74814 q = 1) (hb : d231344 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74814, d231344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59840 q ha hb
    | true =>
      simp only [d74814, d231344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74815 q = 1) (hb : d231345 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74815, d231345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74815, d231345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74816 q = 1) (hb : d231346 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74816, d231346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74816, d231346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74817 q = 1) (hb : d231347 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74817, d231347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74817, d231347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74818 q = 1) (hb : d231348 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74818, d231348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74818, d231348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74819 q = 1) (hb : d231349 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74819, d231349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74819, d231349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59842 (p : Pattern) (ha : d74825 p = 1) (hb : d231355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74820 q = 1) (hb : d231350 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74820, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59841 q ha hb
    | true =>
      simp only [d74820, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74821 q = 1) (hb : d231351 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74821, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74821, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74822 q = 1) (hb : d231352 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74822, d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74822, d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74823 q = 1) (hb : d231353 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74823, d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74823, d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74824 q = 1) (hb : d231354 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74824, d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74824, d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74825 q = 1) (hb : d231355 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74825, d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74825, d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59843 (p : Pattern) (ha : d74831 p = 1) (hb : d231361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74826 q = 1) (hb : d231356 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74826, d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59842 q ha hb
    | true =>
      simp only [d74826, d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74827 q = 1) (hb : d231357 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74827, d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74827, d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74828 q = 1) (hb : d231358 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74828, d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74829 q = 1) (hb : d231359 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74829, d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74830 q = 1) (hb : d231360 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74830, d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74831 q = 1) (hb : d231361 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74831, d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59844 (p : Pattern) (ha : d74837 p = 1) (hb : d231367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d231362 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59843 q ha hb
    | true =>
      simp only [d74832, d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d231363 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d231364 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d231365 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d231366 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d231367 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74837, d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59845 (p : Pattern) (ha : d74843 p = 1) (hb : d231373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d231368 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59844 q ha hb
    | true =>
      simp only [d74838, d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d231369 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d231370 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d231371 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d231372 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d231373 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59846 (p : Pattern) (ha : d74849 p = 1) (hb : d231379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d231374 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59845 q ha hb
    | true =>
      simp only [d74844, d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d231375 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d231376 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d231377 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d231378 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d231379 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59847 (p : Pattern) (ha : d211387 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d211382 q = 1) (hb : d227686 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d211382, d227686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211382, d227686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211383 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d211383, d227687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211383, d227687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211384 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d211384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211385 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d211385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d211386 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d211386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d211387 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d211387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro59848 (p : Pattern) (ha : d211393 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211388 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d211388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59847 q ha hb
    | true =>
      simp only [d211388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211389 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d211389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211390 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d211390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211391 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d211391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211392 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d211392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211393 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d211393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59849 (p : Pattern) (ha : d211399 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211394 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d211394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59848 q ha hb
    | true =>
      simp only [d211394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211395 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d211395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211396 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d211396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211397 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d211397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211398 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d211398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211399 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d211399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59850 (p : Pattern) (ha : d211405 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211400 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d211400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59849 q ha hb
    | true =>
      simp only [d211400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211401 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d211401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211402 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d211402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211403 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d211403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211404 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d211404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211405 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d211405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59851 (p : Pattern) (ha : d211411 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211406 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d211406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59850 q ha hb
    | true =>
      simp only [d211406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211407 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d211407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211408 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d211408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211409 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d211409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211410 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d211410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211411 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d211411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59852 (p : Pattern) (ha : d227687 p = 1) (hb : d231355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231349 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d227686 q = 1) (hb : d231350 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d227686, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d227686, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d227687 q = 1) (hb : d231351 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d227687, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d227687, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d227687 q = 1) (hb : d231352 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d227687 q = 1) (hb : d231353 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d227687 q = 1) (hb : d231354 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d227687 q = 1) (hb : d231355 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro59853 (p : Pattern) (ha : d227687 p = 1) (hb : d231361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d227687 q = 1) (hb : d231356 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59852 q ha hb
    | true =>
      simp only [d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d227687 q = 1) (hb : d231357 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d227687 q = 1) (hb : d231358 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d227687 q = 1) (hb : d231359 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d227687 q = 1) (hb : d231360 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d227687 q = 1) (hb : d231361 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59854 (p : Pattern) (ha : d227687 p = 1) (hb : d231367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d227687 q = 1) (hb : d231362 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59853 q ha hb
    | true =>
      simp only [d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d227687 q = 1) (hb : d231363 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d227687 q = 1) (hb : d231364 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d227687 q = 1) (hb : d231365 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d227687 q = 1) (hb : d231366 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d227687 q = 1) (hb : d231367 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59855 (p : Pattern) (ha : d227687 p = 1) (hb : d231373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d227687 q = 1) (hb : d231368 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59854 q ha hb
    | true =>
      simp only [d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d227687 q = 1) (hb : d231369 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d227687 q = 1) (hb : d231370 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d227687 q = 1) (hb : d231371 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d227687 q = 1) (hb : d231372 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d227687 q = 1) (hb : d231373 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59856 (p : Pattern) (ha : d227687 p = 1) (hb : d231379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d227687 q = 1) (hb : d231374 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59855 q ha hb
    | true =>
      simp only [d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d227687 q = 1) (hb : d231375 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d227687 q = 1) (hb : d231376 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d227687 q = 1) (hb : d231377 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d227687 q = 1) (hb : d231378 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d227687 q = 1) (hb : d231379 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59857 (p : Pattern) (ha : d9381 p = 1) (hb : d208035 p = 1) : d200353 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d23 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9381 q = 1) (hb : d208035 q = 1) : d200353 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d208035, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9381, d208035, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59858 (p : Pattern) (ha : d16081 p = 1) (hb : d208035 p = 1) : d200533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59857 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d208035 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d208035 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d208035 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12495 q = 1) (hb : d208035 q = 1) : d200358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d208035 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16081 q = 1) (hb : d208035 q = 1) : d200533 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d200533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16081, d200533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59859 (p : Pattern) (ha : d23140 p = 1) (hb : d208035 p = 1) : d209547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d208035 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23135 q = 1) (hb : d208035 q = 1) : d209542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59858 q ha hb
    | true =>
      simp only [d23135, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23136 q = 1) (hb : d208035 q = 1) : d209543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23137 q = 1) (hb : d208035 q = 1) : d209544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d208035 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23138 q = 1) (hb : d208035 q = 1) : d209545 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23138, d209545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23138, d209545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d208035 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23139 q = 1) (hb : d208035 q = 1) : d209546 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23139, d209546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23139, d209546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23140 q = 1) (hb : d208035 q = 1) : d209547 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23140, d209547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23140, d209547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro59860 (p : Pattern) (ha : d23146 p = 1) (hb : d208035 p = 1) : d209553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59859 q ha hb
    | true =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d208035 q = 1) : d209551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23145 q = 1) (hb : d208035 q = 1) : d209552 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23145, d209552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23145, d209552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23146 q = 1) (hb : d208035 q = 1) : d209553 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23146, d209553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23146, d209553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro59861 (p : Pattern) (ha : d208035 p = 1) (hb : d211086 p = 1) : d209559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d208035 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d208035 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d208035 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23147 q = 1) (hb : d208035 q = 1) : d209554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59860 q ha hb
    | true =>
      simp only [d23147, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211082 q = 1) : d209555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211082, d209555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211082, d209555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d208035 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211083 q = 1) : d209556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211083, d209556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211083, d209556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211084 q = 1) : d209557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211084, d209557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211084, d209557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d211085 q = 1) : d209558 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211085, d209558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211085, d209558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208035 q = 1) (hb : d211086 q = 1) : d209559 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211086, d209559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211086, d209559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59862 (p : Pattern) (ha : d23153 p = 1) (hb : d208035 p = 1) : d209560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59859 q ha hb
    | true =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d208035 q = 1) : d209551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23145 q = 1) (hb : d208035 q = 1) : d209552 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23145, d209552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23145, d209552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23153 q = 1) (hb : d208035 q = 1) : d209560 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23153, d209560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23153, d209560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro59863 (p : Pattern) (ha : d208035 p = 1) (hb : d211091 p = 1) : d209566 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d208035 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d208035 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d208035 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23147 q = 1) (hb : d208035 q = 1) : d209554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59860 q ha hb
    | true =>
      simp only [d23147, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211082 q = 1) : d209555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211082, d209555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211082, d209555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d208035 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211083 q = 1) : d209556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211083, d209556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211083, d209556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211084 q = 1) : d209557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211084, d209557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211084, d209557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d211085 q = 1) : d209558 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211085, d209558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211085, d209558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d208035 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d208035 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d208035 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23154 q = 1) (hb : d208035 q = 1) : d209561 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59862 q ha hb
    | true =>
      simp only [d23154, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d211087 q = 1) : d209562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211087, d209562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d211087, d209562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d208035 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d208035 q = 1) (hb : d211088 q = 1) : d209563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211088, d209563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211088, d209563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d208035 q = 1) (hb : d211089 q = 1) : d209564 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211089, d209564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211089, d209564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208035 q = 1) (hb : d211090 q = 1) : d209565 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211090, d209565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211090, d209565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d208035 q = 1) (hb : d211091 q = 1) : d209566 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211091, d209566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211091, d209566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59864 (p : Pattern) (ha : d208035 p = 1) (hb : d211098 p = 1) : d209573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d208035 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23154 q = 1) (hb : d208035 q = 1) : d209561 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59862 q ha hb
    | true =>
      simp only [d23154, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d211087 q = 1) : d209562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211087, d209562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211087, d209562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d208035 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211088 q = 1) : d209563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211088, d209563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211088, d209563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211096 q = 1) : d209571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211096, d209571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211096, d209571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211097 q = 1) : d209572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211097, d209572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211097, d209572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211098 q = 1) : d209573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211098, d209573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211098, d209573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59865 (p : Pattern) (ha : d16166 p = 1) (hb : d208035 p = 1) : d200620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d208035 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59857 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59857 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d208035 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d208035 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d208035 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d208035 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12603 q = 1) (hb : d208035 q = 1) : d200426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d208035 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16166 q = 1) (hb : d208035 q = 1) : d200620 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d200620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16166, d200620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59866 (p : Pattern) (ha : d23177 p = 1) (hb : d208035 p = 1) : d209584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d208035 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23172 q = 1) (hb : d208035 q = 1) : d209579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59865 q ha hb
    | true =>
      simp only [d23172, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23173 q = 1) (hb : d208035 q = 1) : d209580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23174 q = 1) (hb : d208035 q = 1) : d209581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d208035 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23175 q = 1) (hb : d208035 q = 1) : d209582 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23175, d209582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23175, d209582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d208035 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23176 q = 1) (hb : d208035 q = 1) : d209583 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23176, d209583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23176, d209583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23177 q = 1) (hb : d208035 q = 1) : d209584 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23177, d209584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23177, d209584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro59867 (p : Pattern) (ha : d23183 p = 1) (hb : d208035 p = 1) : d209590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23178 q = 1) (hb : d208035 q = 1) : d209585 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23178, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59866 q ha hb
    | true =>
      simp only [d23178, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23179 q = 1) (hb : d208035 q = 1) : d209586 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23179, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23179, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d208035 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23180 q = 1) (hb : d208035 q = 1) : d209587 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23180, d209587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23180, d209587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23181 q = 1) (hb : d208035 q = 1) : d209588 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23181, d209588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23181, d209588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23182 q = 1) (hb : d208035 q = 1) : d209589 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23182, d209589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23182, d209589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23183 q = 1) (hb : d208035 q = 1) : d209590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23183, d209590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23183, d209590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro59868 (p : Pattern) (ha : d208035 p = 1) (hb : d211108 p = 1) : d209596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d208035 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23184 q = 1) (hb : d208035 q = 1) : d209591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23184, d209591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59867 q ha hb
    | true =>
      simp only [d23184, d209591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d211104 q = 1) : d209592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211104, d209592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211104, d209592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d208035 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211105 q = 1) : d209593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211105, d209593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211105, d209593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211106 q = 1) : d209594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211106, d209594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211106, d209594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211107 q = 1) : d209595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211107, d209595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211107, d209595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211108 q = 1) : d209596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211108, d209596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211108, d209596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59869 (p : Pattern) (ha : d208035 p = 1) (hb : d211114 p = 1) : d209602 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d208035 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d211092 q = 1) : d209567 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211092, d209567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59861 q ha hb
    | true =>
      simp only [d211092, d209567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59863 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d208035 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d211093 q = 1) : d209568 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211093, d209568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211093, d209568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211094 q = 1) : d209569 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211094, d209569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211094, d209569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211095 q = 1) : d209570 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211095, d209570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211095, d209570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211099 q = 1) : d209574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211099, d209574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211099, d209574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59864 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211100 q = 1) : d209575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211100, d209575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211100, d209575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d211101 q = 1) : d209576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211101, d209576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211101, d209576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d208035 q = 1) (hb : d211102 q = 1) : d209577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211102, d209577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211102, d209577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208035 q = 1) (hb : d211103 q = 1) : d209578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211103, d209578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211103, d209578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208035 q = 1) (hb : d211109 q = 1) : d209597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211109, d209597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211109, d209597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59868 q ha hb
  have h13 (q : Pattern) (ha : d208035 q = 1) (hb : d211110 q = 1) : d209598 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211110, d209598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211110, d209598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d211111 q = 1) : d209599 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211111, d209599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211111, d209599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d211112 q = 1) : d209600 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211112, d209600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211112, d209600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d208035 q = 1) (hb : d211113 q = 1) : d209601 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211113, d209601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211113, d209601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208035 q = 1) (hb : d211114 q = 1) : d209602 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211114, d209602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211114, d209602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro59870 (p : Pattern) (ha : d23205 p = 1) (hb : d208035 p = 1) : d209612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208035 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23147 q = 1) (hb : d208035 q = 1) : d209554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59860 q ha hb
    | true =>
      simp only [d23147, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23201 q = 1) (hb : d208035 q = 1) : d209608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23201, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23202 q = 1) (hb : d208035 q = 1) : d209609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23202, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23203 q = 1) (hb : d208035 q = 1) : d209610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23203, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23204 q = 1) (hb : d208035 q = 1) : d209611 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23205 q = 1) (hb : d208035 q = 1) : d209612 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23205, d209612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23205, d209612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro59871 (p : Pattern) (ha : d23212 p = 1) (hb : d208035 p = 1) : d209619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208035 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23147 q = 1) (hb : d208035 q = 1) : d209554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59860 q ha hb
    | true =>
      simp only [d23147, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23201 q = 1) (hb : d208035 q = 1) : d209608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23201, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23202 q = 1) (hb : d208035 q = 1) : d209609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23202, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23203 q = 1) (hb : d208035 q = 1) : d209610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23203, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23204 q = 1) (hb : d208035 q = 1) : d209611 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d208035 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23154 q = 1) (hb : d208035 q = 1) : d209561 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59862 q ha hb
    | true =>
      simp only [d23154, d209561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23208 q = 1) (hb : d208035 q = 1) : d209615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23208, d209615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23209 q = 1) (hb : d208035 q = 1) : d209616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23209, d209616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23210 q = 1) (hb : d208035 q = 1) : d209617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23210, d209617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23211 q = 1) (hb : d208035 q = 1) : d209618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23211, d209618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23212 q = 1) (hb : d208035 q = 1) : d209619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23212, d209619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23212, d209619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro59872 (p : Pattern) (ha : d23297 p = 1) (hb : d208035 p = 1) : d209680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208035 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23147 q = 1) (hb : d208035 q = 1) : d209554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59860 q ha hb
    | true =>
      simp only [d23147, d209554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23201 q = 1) (hb : d208035 q = 1) : d209608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23201, d209608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23202 q = 1) (hb : d208035 q = 1) : d209609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23202, d209609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23203 q = 1) (hb : d208035 q = 1) : d209610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23203, d209610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23204 q = 1) (hb : d208035 q = 1) : d209611 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d209611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d208035 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23297 q = 1) (hb : d208035 q = 1) : d209680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23297, d209680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23297, d209680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59873 (p : Pattern) (ha : d23217 p = 1) (hb : d208035 p = 1) : d209624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59859 q ha hb
    | true =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d208035 q = 1) : d209551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23216 q = 1) (hb : d208035 q = 1) : d209623 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23216, d209623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23216, d209623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23217 q = 1) (hb : d208035 q = 1) : d209624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23217, d209624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23217, d209624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro59874 (p : Pattern) (ha : d23224 p = 1) (hb : d208035 p = 1) : d209631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59859 q ha hb
    | true =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23222 q = 1) (hb : d208035 q = 1) : d209629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23222, d209629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23222, d209629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23223 q = 1) (hb : d208035 q = 1) : d209630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23223, d209630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23223, d209630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23224 q = 1) (hb : d208035 q = 1) : d209631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23224, d209631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23224, d209631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro59875 (p : Pattern) (ha : d23230 p = 1) (hb : d208035 p = 1) : d200523 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23228 q = 1) (hb : d208034 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23228, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23229 q = 1) (hb : d208034 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23229, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d5449 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23230 q = 1) (hb : d208035 q = 1) : d200523 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23230, d208035, d200523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23230, d208035, d200523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59876 (p : Pattern) (ha : d23236 p = 1) (hb : d208035 p = 1) : d209635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23231 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
    | true =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23232 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23233 q = 1) (hb : d208035 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23234 q = 1) (hb : d208035 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23234, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9382 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59857 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9384 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12493 q = 1) (hb : d208035 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12494 q = 1) (hb : d208035 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23235 q = 1) (hb : d208035 q = 1) : d200528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23235, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23235, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28 q = 1) (hb : d208035 q = 1) : d28 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12495 q = 1) (hb : d208035 q = 1) : d200358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12495, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23236 q = 1) (hb : d208035 q = 1) : d209635 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23236, d209635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23236, d209635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro59877 (p : Pattern) (ha : d23242 p = 1) (hb : d208035 p = 1) : d209641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23237 q = 1) (hb : d208035 q = 1) : d209636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23237, d209636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59876 q ha hb
    | true =>
      simp only [d23237, d209636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59858 q ha hb
  have h2 (q : Pattern) (ha : d23238 q = 1) (hb : d208035 q = 1) : d209637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23238, d209637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23238, d209637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23239 q = 1) (hb : d208035 q = 1) : d209638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23239, d209638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23239, d209638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d208035 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23135 q = 1) (hb : d208035 q = 1) : d209542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59858 q ha hb
    | true =>
      simp only [d23135, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23136 q = 1) (hb : d208035 q = 1) : d209543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23137 q = 1) (hb : d208035 q = 1) : d209544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23240 q = 1) (hb : d208035 q = 1) : d209639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23240, d209639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23240, d209639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d208035 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23138 q = 1) (hb : d208035 q = 1) : d209545 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23138, d209545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23138, d209545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23241 q = 1) (hb : d208035 q = 1) : d209640 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23241, d209640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23241, d209640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23242 q = 1) (hb : d208035 q = 1) : d209641 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23242, d209641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23242, d209641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro59878 (p : Pattern) (ha : d23248 p = 1) (hb : d208035 p = 1) : d209647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23243 q = 1) (hb : d208035 q = 1) : d209642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23243, d209642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59877 q ha hb
    | true =>
      simp only [d23243, d209642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23244 q = 1) (hb : d208035 q = 1) : d209643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23244, d209643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23244, d209643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23141 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59859 q ha hb
    | true =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23142 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23245 q = 1) (hb : d208035 q = 1) : d209644 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23245, d209644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23245, d209644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23246 q = 1) (hb : d208035 q = 1) : d209645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23246, d209645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23246, d209645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23247 q = 1) (hb : d208035 q = 1) : d209646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23247, d209646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23247, d209646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23248 q = 1) (hb : d208035 q = 1) : d209647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23248, d209647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23248, d209647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59879 (p : Pattern) (ha : d23268 p = 1) (hb : d208035 p = 1) : d209653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59859 q ha hb
    | true =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23265 q = 1) (hb : d208035 q = 1) : d209650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23265, d209650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23265, d209650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23266 q = 1) (hb : d208035 q = 1) : d209651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23266, d209651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23266, d209651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23267 q = 1) (hb : d208035 q = 1) : d209652 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23267, d209652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23267, d209652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23268 q = 1) (hb : d208035 q = 1) : d209653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23268, d209653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23268, d209653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59880 (p : Pattern) (ha : d208035 p = 1) (hb : d211124 p = 1) : d209659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d208035 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23218 q = 1) (hb : d208035 q = 1) : d209625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23218, d209625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59873 q ha hb
    | true =>
      simp only [d23218, d209625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23219 q = 1) (hb : d208035 q = 1) : d209626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23219, d209626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23219, d209626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23220 q = 1) (hb : d208035 q = 1) : d209627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23220, d209627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23220, d209627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23221 q = 1) (hb : d208035 q = 1) : d209628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23221, d209628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23221, d209628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d208035 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23225 q = 1) (hb : d208035 q = 1) : d209632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23225, d209632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59874 q ha hb
    | true =>
      simp only [d23225, d209632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23226 q = 1) (hb : d208035 q = 1) : d209633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23226, d209633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23226, d209633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23227 q = 1) (hb : d208035 q = 1) : d209634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23227, d209634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23227, d209634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23249 q = 1) (hb : d208035 q = 1) : d209648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23249, d209648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59878 q ha hb
    | true =>
      simp only [d23249, d209648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59860 q ha hb
  have h11 (q : Pattern) (ha : d208035 q = 1) (hb : d211120 q = 1) : d209649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211120, d209649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211120, d209649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d23269 q = 1) (hb : d208035 q = 1) : d209654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23269, d209654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59879 q ha hb
    | true =>
      simp only [d23269, d209654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23270 q = 1) (hb : d208035 q = 1) : d209655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23270, d209655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23270, d209655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d211121 q = 1) : d209656 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211121, d209656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211121, d209656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d211122 q = 1) : d209657 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211122, d209657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211122, d209657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d208035 q = 1) (hb : d211123 q = 1) : d209658 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211123, d209658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211123, d209658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208035 q = 1) (hb : d211124 q = 1) : d209659 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211124, d209659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211124, d209659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro59881 (p : Pattern) (ha : d23275 p = 1) (hb : d208035 p = 1) : d209660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59859 q ha hb
    | true =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23144 q = 1) (hb : d208035 q = 1) : d209551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23144, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23144, d209551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23216 q = 1) (hb : d208035 q = 1) : d209623 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23216, d209623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23216, d209623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23275 q = 1) (hb : d208035 q = 1) : d209660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23275, d209660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23275, d209660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro59882 (p : Pattern) (ha : d23280 p = 1) (hb : d208035 p = 1) : d209665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59859 q ha hb
    | true =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208035 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23143 q = 1) (hb : d208035 q = 1) : d209550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23143, d209550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23222 q = 1) (hb : d208035 q = 1) : d209629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23222, d209629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23222, d209629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23223 q = 1) (hb : d208035 q = 1) : d209630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23223, d209630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23223, d209630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23280 q = 1) (hb : d208035 q = 1) : d209665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23280, d209665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23280, d209665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro59883 (p : Pattern) (ha : d23284 p = 1) (hb : d208035 p = 1) : d209669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23243 q = 1) (hb : d208035 q = 1) : d209642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23243, d209642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59877 q ha hb
    | true =>
      simp only [d23243, d209642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23244 q = 1) (hb : d208035 q = 1) : d209643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23244, d209643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23244, d209643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23141 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59859 q ha hb
    | true =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23142 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23245 q = 1) (hb : d208035 q = 1) : d209644 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23245, d209644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23245, d209644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23246 q = 1) (hb : d208035 q = 1) : d209645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23246, d209645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23246, d209645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23247 q = 1) (hb : d208035 q = 1) : d209646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23247, d209646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23247, d209646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23284 q = 1) (hb : d208035 q = 1) : d209669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23284, d209669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23284, d209669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59884 (p : Pattern) (ha : d23289 p = 1) (hb : d208035 p = 1) : d209672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23141 q = 1) (hb : d208035 q = 1) : d209548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59859 q ha hb
    | true =>
      simp only [d23141, d209548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23142 q = 1) (hb : d208035 q = 1) : d209549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23142, d209549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23265 q = 1) (hb : d208035 q = 1) : d209650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23265, d209650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23265, d209650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23266 q = 1) (hb : d208035 q = 1) : d209651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23266, d209651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23266, d209651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23267 q = 1) (hb : d208035 q = 1) : d209652 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23267, d209652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23267, d209652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23289 q = 1) (hb : d208035 q = 1) : d209672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23289, d209672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23289, d209672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59885 (p : Pattern) (ha : d208035 p = 1) (hb : d211129 p = 1) : d209678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d208035 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23218 q = 1) (hb : d208035 q = 1) : d209625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23218, d209625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59873 q ha hb
    | true =>
      simp only [d23218, d209625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23219 q = 1) (hb : d208035 q = 1) : d209626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23219, d209626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23219, d209626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23220 q = 1) (hb : d208035 q = 1) : d209627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23220, d209627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23220, d209627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23221 q = 1) (hb : d208035 q = 1) : d209628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23221, d209628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23221, d209628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d208035 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23225 q = 1) (hb : d208035 q = 1) : d209632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23225, d209632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59874 q ha hb
    | true =>
      simp only [d23225, d209632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23226 q = 1) (hb : d208035 q = 1) : d209633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23226, d209633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23226, d209633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23227 q = 1) (hb : d208035 q = 1) : d209634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23227, d209634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23227, d209634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23249 q = 1) (hb : d208035 q = 1) : d209648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23249, d209648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59878 q ha hb
    | true =>
      simp only [d23249, d209648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59860 q ha hb
  have h11 (q : Pattern) (ha : d208035 q = 1) (hb : d211120 q = 1) : d209649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211120, d209649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211120, d209649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d23269 q = 1) (hb : d208035 q = 1) : d209654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23269, d209654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59879 q ha hb
    | true =>
      simp only [d23269, d209654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23270 q = 1) (hb : d208035 q = 1) : d209655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23270, d209655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23270, d209655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d211121 q = 1) : d209656 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211121, d209656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211121, d209656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d211122 q = 1) : d209657 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211122, d209657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211122, d209657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d208035 q = 1) (hb : d211123 q = 1) : d209658 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211123, d209658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211123, d209658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d208035 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d23276 q = 1) (hb : d208035 q = 1) : d209661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23276, d209661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59881 q ha hb
    | true =>
      simp only [d23276, d209661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23277 q = 1) (hb : d208035 q = 1) : d209662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23277, d209662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23277, d209662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d23278 q = 1) (hb : d208035 q = 1) : d209663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23278, d209663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d23278, d209663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d23279 q = 1) (hb : d208035 q = 1) : d209664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23279, d209664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23279, d209664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d208035 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d23281 q = 1) (hb : d208035 q = 1) : d209666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23281, d209666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59882 q ha hb
    | true =>
      simp only [d23281, d209666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d23282 q = 1) (hb : d208035 q = 1) : d209667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23282, d209667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23282, d209667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d23283 q = 1) (hb : d208035 q = 1) : d209668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23283, d209668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23283, d209668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d23285 q = 1) (hb : d208035 q = 1) : d209670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23285, d209670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59883 q ha hb
    | true =>
      simp only [d23285, d209670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59862 q ha hb
  have h27 (q : Pattern) (ha : d208035 q = 1) (hb : d211125 q = 1) : d209671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211125, d209671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d211125, d209671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d23290 q = 1) (hb : d208035 q = 1) : d209673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23290, d209673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59884 q ha hb
    | true =>
      simp only [d23290, d209673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d23291 q = 1) (hb : d208035 q = 1) : d209674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23291, d209674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d23291, d209674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d208035 q = 1) (hb : d211126 q = 1) : d209675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211126, d209675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d211126, d209675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d208035 q = 1) (hb : d211127 q = 1) : d209676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211127, d209676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d211127, d209676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d208035 q = 1) (hb : d211128 q = 1) : d209677 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211128, d209677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d211128, d209677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d208035 q = 1) (hb : d211129 q = 1) : d209678 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211129, d209678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211129, d209678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro59886 (p : Pattern) (ha : d208035 p = 1) (hb : d211136 p = 1) : d209687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23285 q = 1) (hb : d208035 q = 1) : d209670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23285, d209670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59883 q ha hb
    | true =>
      simp only [d23285, d209670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59862 q ha hb
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d211125 q = 1) : d209671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211125, d209671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211125, d209671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23290 q = 1) (hb : d208035 q = 1) : d209673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23290, d209673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59884 q ha hb
    | true =>
      simp only [d23290, d209673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23291 q = 1) (hb : d208035 q = 1) : d209674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23291, d209674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23291, d209674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211126 q = 1) : d209675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211126, d209675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211126, d209675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211134 q = 1) : d209685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211134, d209685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211134, d209685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211135 q = 1) : d209686 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211135, d209686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211135, d209686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211136 q = 1) : d209687 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211136, d209687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211136, d209687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59887 (p : Pattern) (ha : d23315 p = 1) (hb : d208035 p = 1) : d209693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23310 q = 1) (hb : d208035 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
  have h2 (q : Pattern) (ha : d23231 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
    | true =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23311 q = 1) (hb : d208035 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23311, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23232 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23312 q = 1) (hb : d208035 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23312, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23313 q = 1) (hb : d208035 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23313, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12599 q = 1) (hb : d208035 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59857 q ha hb
  have h8 (q : Pattern) (ha : d9382 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59857 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12600 q = 1) (hb : d208035 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9384 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12601 q = 1) (hb : d208035 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12602 q = 1) (hb : d208035 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23314 q = 1) (hb : d208035 q = 1) : d200615 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23314, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23314, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69 q = 1) (hb : d208035 q = 1) : d69 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12603 q = 1) (hb : d208035 q = 1) : d200426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12603, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23315 q = 1) (hb : d208035 q = 1) : d209693 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23315, d209693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23315, d209693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro59888 (p : Pattern) (ha : d23321 p = 1) (hb : d208035 p = 1) : d209699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23316 q = 1) (hb : d208035 q = 1) : d209694 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23316, d209694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59887 q ha hb
    | true =>
      simp only [d23316, d209694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59865 q ha hb
  have h2 (q : Pattern) (ha : d23317 q = 1) (hb : d208035 q = 1) : d209695 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23317, d209695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23317, d209695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23318 q = 1) (hb : d208035 q = 1) : d209696 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23318, d209696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23318, d209696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d208035 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23172 q = 1) (hb : d208035 q = 1) : d209579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59865 q ha hb
    | true =>
      simp only [d23172, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23173 q = 1) (hb : d208035 q = 1) : d209580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23174 q = 1) (hb : d208035 q = 1) : d209581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23319 q = 1) (hb : d208035 q = 1) : d209697 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23319, d209697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23319, d209697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d208035 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23175 q = 1) (hb : d208035 q = 1) : d209582 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23175, d209582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23175, d209582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23320 q = 1) (hb : d208035 q = 1) : d209698 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23320, d209698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23320, d209698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23321 q = 1) (hb : d208035 q = 1) : d209699 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23321, d209699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23321, d209699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro59889 (p : Pattern) (ha : d23327 p = 1) (hb : d208035 p = 1) : d209705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23322 q = 1) (hb : d208035 q = 1) : d209700 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23322, d209700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59888 q ha hb
    | true =>
      simp only [d23322, d209700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23323 q = 1) (hb : d208035 q = 1) : d209701 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23323, d209701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23323, d209701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23178 q = 1) (hb : d208035 q = 1) : d209585 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23178, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59866 q ha hb
    | true =>
      simp only [d23178, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23179 q = 1) (hb : d208035 q = 1) : d209586 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23179, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23179, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23324 q = 1) (hb : d208035 q = 1) : d209702 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23324, d209702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23324, d209702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23325 q = 1) (hb : d208035 q = 1) : d209703 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23325, d209703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23325, d209703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23326 q = 1) (hb : d208035 q = 1) : d209704 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23326, d209704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23326, d209704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23327 q = 1) (hb : d208035 q = 1) : d209705 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23327, d209705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23327, d209705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59890 (p : Pattern) (ha : d23347 p = 1) (hb : d208035 p = 1) : d209711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23178 q = 1) (hb : d208035 q = 1) : d209585 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23178, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59866 q ha hb
    | true =>
      simp only [d23178, d209585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23179 q = 1) (hb : d208035 q = 1) : d209586 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23179, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23179, d209586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23344 q = 1) (hb : d208035 q = 1) : d209708 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23344, d209708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23344, d209708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23345 q = 1) (hb : d208035 q = 1) : d209709 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23345, d209709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23345, d209709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23346 q = 1) (hb : d208035 q = 1) : d209710 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23346, d209710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23346, d209710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23347 q = 1) (hb : d208035 q = 1) : d209711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23347, d209711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23347, d209711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59891 (p : Pattern) (ha : d208035 p = 1) (hb : d211146 p = 1) : d209717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23328 q = 1) (hb : d208035 q = 1) : d209706 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23328, d209706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59889 q ha hb
    | true =>
      simp only [d23328, d209706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59867 q ha hb
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d211142 q = 1) : d209707 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211142, d209707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211142, d209707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23348 q = 1) (hb : d208035 q = 1) : d209712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23348, d209712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59890 q ha hb
    | true =>
      simp only [d23348, d209712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23349 q = 1) (hb : d208035 q = 1) : d209713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23349, d209713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23349, d209713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211143 q = 1) : d209714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211143, d209714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211143, d209714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211144 q = 1) : d209715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211144, d209715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211144, d209715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211145 q = 1) : d209716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211145, d209716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211145, d209716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211146 q = 1) : d209717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211146, d209717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211146, d209717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59892 (p : Pattern) (ha : d208035 p = 1) (hb : d211152 p = 1) : d209723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23206 q = 1) (hb : d208035 q = 1) : d209613 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23206, d209613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23206, d209613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59870 q ha hb
  have h2 (q : Pattern) (ha : d23207 q = 1) (hb : d208035 q = 1) : d209614 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23207, d209614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23207, d209614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23213 q = 1) (hb : d208035 q = 1) : d209620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23213, d209620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59870 q ha hb
    | true =>
      simp only [d23213, d209620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59871 q ha hb
  have h4 (q : Pattern) (ha : d23214 q = 1) (hb : d208035 q = 1) : d209621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23214, d209621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23214, d209621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23215 q = 1) (hb : d208035 q = 1) : d209622 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d23215, d209622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23215, d209622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211130 q = 1) : d209679 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211130, d209679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59880 q ha hb
    | true =>
      simp only [d211130, d209679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59885 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d208035 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23298 q = 1) (hb : d208035 q = 1) : d209681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23298, d209681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59872 q ha hb
    | true =>
      simp only [d23298, d209681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d211131 q = 1) : d209682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211131, d209682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211131, d209682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208035 q = 1) (hb : d211132 q = 1) : d209683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211132, d209683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211132, d209683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d208035 q = 1) (hb : d211133 q = 1) : d209684 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211133, d209684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211133, d209684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208035 q = 1) (hb : d211137 q = 1) : d209688 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211137, d209688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211137, d209688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59886 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d208035 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d211138 q = 1) : d209689 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211138, d209689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211138, d209689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d211139 q = 1) : d209690 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211139, d209690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211139, d209690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d208035 q = 1) (hb : d211140 q = 1) : d209691 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211140, d209691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211140, d209691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d208035 q = 1) (hb : d211141 q = 1) : d209692 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211141, d209692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211141, d209692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208035 q = 1) (hb : d211147 q = 1) : d209718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211147, d209718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211147, d209718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59891 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d208035 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d208035 q = 1) (hb : d211148 q = 1) : d209719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211148, d209719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d211148, d209719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d208035 q = 1) (hb : d211149 q = 1) : d209720 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211149, d209720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d211149, d209720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d208035 q = 1) (hb : d211150 q = 1) : d209721 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211150, d209721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211150, d209721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d208035 q = 1) (hb : d211151 q = 1) : d209722 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211151, d209722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d211151, d209722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d208035 q = 1) (hb : d211152 q = 1) : d209723 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211152, d209723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211152, d209723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro59893 (p : Pattern) (ha : d208035 p = 1) (hb : d211158 p = 1) : d209729 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d208035 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d211115 q = 1) : d209603 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211115, d209603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211115, d209603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59869 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d211116 q = 1) : d209604 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211116, d209604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211116, d209604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d211117 q = 1) : d209605 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211117, d209605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211117, d209605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211118 q = 1) : d209606 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211118, d209606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211118, d209606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211119 q = 1) : d209607 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211119, d209607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211119, d209607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211153 q = 1) : d209724 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211153, d209724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211153, d209724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59892 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211154 q = 1) : d209725 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211154, d209725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211154, d209725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d211155 q = 1) : d209726 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211155, d209726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211155, d209726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208035 q = 1) (hb : d211156 q = 1) : d209727 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211156, d209727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211156, d209727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208035 q = 1) (hb : d211157 q = 1) : d209728 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211157, d209728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211157, d209728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208035 q = 1) (hb : d211158 q = 1) : d209729 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211158, d209729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211158, d209729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro59894 (p : Pattern) (ha : d23368 p = 1) (hb : d208035 p = 1) : d209732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23237 q = 1) (hb : d208035 q = 1) : d209636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23237, d209636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59876 q ha hb
    | true =>
      simp only [d23237, d209636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59858 q ha hb
  have h2 (q : Pattern) (ha : d23238 q = 1) (hb : d208035 q = 1) : d209637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23238, d209637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23238, d209637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23239 q = 1) (hb : d208035 q = 1) : d209638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23239, d209638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23239, d209638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d208035 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23135 q = 1) (hb : d208035 q = 1) : d209542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59858 q ha hb
    | true =>
      simp only [d23135, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23136 q = 1) (hb : d208035 q = 1) : d209543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23137 q = 1) (hb : d208035 q = 1) : d209544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23240 q = 1) (hb : d208035 q = 1) : d209639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23240, d209639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23240, d209639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23366 q = 1) (hb : d208035 q = 1) : d209730 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23366, d209730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23366, d209730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23367 q = 1) (hb : d208035 q = 1) : d209731 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23367, d209731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23367, d209731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23368 q = 1) (hb : d208035 q = 1) : d209732 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23368, d209732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23368, d209732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro59895 (p : Pattern) (ha : d23372 p = 1) (hb : d208035 p = 1) : d209736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d208035 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23135 q = 1) (hb : d208035 q = 1) : d209542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59858 q ha hb
    | true =>
      simp only [d23135, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23136 q = 1) (hb : d208035 q = 1) : d209543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23137 q = 1) (hb : d208035 q = 1) : d209544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23366 q = 1) (hb : d208035 q = 1) : d209730 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23366, d209730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23366, d209730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23371 q = 1) (hb : d208035 q = 1) : d209735 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23371, d209735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23371, d209735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23372 q = 1) (hb : d208035 q = 1) : d209736 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23372, d209736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23372, d209736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro59896 (p : Pattern) (ha : d23378 p = 1) (hb : d208035 p = 1) : d209742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208035 q = 1) : d209733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59894 q ha hb
    | true =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208035 q = 1) : d209734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208035 q = 1) : d209739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d208035 q = 1) : d209740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d209740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d209740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23377 q = 1) (hb : d208035 q = 1) : d209741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23377, d209741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23377, d209741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23378 q = 1) (hb : d208035 q = 1) : d209742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23378, d209742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23378, d209742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59897 (p : Pattern) (ha : d23382 p = 1) (hb : d208035 p = 1) : d209746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208035 q = 1) : d209743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d208035 q = 1) : d209744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d209744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d209744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23381 q = 1) (hb : d208035 q = 1) : d209745 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23381, d209745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23381, d209745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23382 q = 1) (hb : d208035 q = 1) : d209746 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23382, d209746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23382, d209746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59898 (p : Pattern) (ha : d23388 p = 1) (hb : d208035 p = 1) : d209752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23383 q = 1) (hb : d208035 q = 1) : d209747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59896 q ha hb
    | true =>
      simp only [d23383, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59897 q ha hb
  have h2 (q : Pattern) (ha : d23384 q = 1) (hb : d208035 q = 1) : d209748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23384, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23385 q = 1) (hb : d208035 q = 1) : d209749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23385, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23386 q = 1) (hb : d208035 q = 1) : d209750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23386, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23387 q = 1) (hb : d208035 q = 1) : d209751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23388 q = 1) (hb : d208035 q = 1) : d209752 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23388, d209752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23388, d209752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59899 (p : Pattern) (ha : d23391 p = 1) (hb : d208035 p = 1) : d209755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208035 q = 1) : d209733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59894 q ha hb
    | true =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208035 q = 1) : d209734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208035 q = 1) : d209739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d208035 q = 1) : d209740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d209740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d209740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23377 q = 1) (hb : d208035 q = 1) : d209741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23377, d209741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23377, d209741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23391 q = 1) (hb : d208035 q = 1) : d209755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23391, d209755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23391, d209755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59900 (p : Pattern) (ha : d23392 p = 1) (hb : d208035 p = 1) : d209756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208035 q = 1) : d209743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d208035 q = 1) : d209744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d209744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d209744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23381 q = 1) (hb : d208035 q = 1) : d209745 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23381, d209745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23381, d209745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23392 q = 1) (hb : d208035 q = 1) : d209756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23392, d209756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23392, d209756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59901 (p : Pattern) (ha : d23398 p = 1) (hb : d208035 p = 1) : d209762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23383 q = 1) (hb : d208035 q = 1) : d209747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59896 q ha hb
    | true =>
      simp only [d23383, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59897 q ha hb
  have h2 (q : Pattern) (ha : d23384 q = 1) (hb : d208035 q = 1) : d209748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23384, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23385 q = 1) (hb : d208035 q = 1) : d209749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23385, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23386 q = 1) (hb : d208035 q = 1) : d209750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23386, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23387 q = 1) (hb : d208035 q = 1) : d209751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23393 q = 1) (hb : d208035 q = 1) : d209757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23393, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59899 q ha hb
    | true =>
      simp only [d23393, d209757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59900 q ha hb
  have h7 (q : Pattern) (ha : d23394 q = 1) (hb : d208035 q = 1) : d209758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23394, d209758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23395 q = 1) (hb : d208035 q = 1) : d209759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23395, d209759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23396 q = 1) (hb : d208035 q = 1) : d209760 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23396, d209760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23397 q = 1) (hb : d208035 q = 1) : d209761 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23397, d209761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23398 q = 1) (hb : d208035 q = 1) : d209762 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23398, d209762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23398, d209762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59902 (p : Pattern) (ha : d23513 p = 1) (hb : d208035 p = 1) : d209835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23383 q = 1) (hb : d208035 q = 1) : d209747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59896 q ha hb
    | true =>
      simp only [d23383, d209747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59897 q ha hb
  have h2 (q : Pattern) (ha : d23384 q = 1) (hb : d208035 q = 1) : d209748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23384, d209748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23385 q = 1) (hb : d208035 q = 1) : d209749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23385, d209749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23386 q = 1) (hb : d208035 q = 1) : d209750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23386, d209750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23387 q = 1) (hb : d208035 q = 1) : d209751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d209751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23508 q = 1) (hb : d208035 q = 1) : d209830 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23508, d209830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59897 q ha hb
    | true =>
      simp only [d23508, d209830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23509 q = 1) (hb : d208035 q = 1) : d209831 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23509, d209831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23509, d209831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23510 q = 1) (hb : d208035 q = 1) : d209832 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23510, d209832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23510, d209832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23511 q = 1) (hb : d208035 q = 1) : d209833 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23511, d209833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23511, d209833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23512 q = 1) (hb : d208035 q = 1) : d209834 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23512, d209834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23512, d209834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23513 q = 1) (hb : d208035 q = 1) : d209835 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23513, d209835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23513, d209835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59903 (p : Pattern) (ha : d23519 p = 1) (hb : d208035 p = 1) : d209841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23508 q = 1) (hb : d208035 q = 1) : d209830 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23508, d209830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59897 q ha hb
    | true =>
      simp only [d23508, d209830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23509 q = 1) (hb : d208035 q = 1) : d209831 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23509, d209831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23509, d209831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23510 q = 1) (hb : d208035 q = 1) : d209832 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23510, d209832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23510, d209832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23511 q = 1) (hb : d208035 q = 1) : d209833 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23511, d209833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23511, d209833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23512 q = 1) (hb : d208035 q = 1) : d209834 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23512, d209834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23512, d209834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23514 q = 1) (hb : d208035 q = 1) : d209836 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23514, d209836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59900 q ha hb
    | true =>
      simp only [d23514, d209836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23515 q = 1) (hb : d208035 q = 1) : d209837 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23515, d209837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23515, d209837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23516 q = 1) (hb : d208035 q = 1) : d209838 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23516, d209838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23516, d209838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23517 q = 1) (hb : d208035 q = 1) : d209839 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23517, d209839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23517, d209839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23518 q = 1) (hb : d208035 q = 1) : d209840 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23518, d209840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23518, d209840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23519 q = 1) (hb : d208035 q = 1) : d209841 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23519, d209841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23519, d209841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59904 (p : Pattern) (ha : d23528 p = 1) (hb : d208035 p = 1) : d209850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23514 q = 1) (hb : d208035 q = 1) : d209836 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23514, d209836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59900 q ha hb
    | true =>
      simp only [d23514, d209836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23515 q = 1) (hb : d208035 q = 1) : d209837 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23515, d209837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23515, d209837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23516 q = 1) (hb : d208035 q = 1) : d209838 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23516, d209838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23516, d209838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23517 q = 1) (hb : d208035 q = 1) : d209839 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23517, d209839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23517, d209839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23518 q = 1) (hb : d208035 q = 1) : d209840 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23518, d209840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23518, d209840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23528 q = 1) (hb : d208035 q = 1) : d209850 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23528, d209850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23528, d209850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59905 (p : Pattern) (ha : d23558 p = 1) (hb : d208035 p = 1) : d209875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d208035 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23172 q = 1) (hb : d208035 q = 1) : d209579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59865 q ha hb
    | true =>
      simp only [d23172, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23173 q = 1) (hb : d208035 q = 1) : d209580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23174 q = 1) (hb : d208035 q = 1) : d209581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23548 q = 1) (hb : d208035 q = 1) : d209865 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23548, d209865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23548, d209865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23557 q = 1) (hb : d208035 q = 1) : d209874 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23557, d209874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23557, d209874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23558 q = 1) (hb : d208035 q = 1) : d209875 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23558, d209875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23558, d209875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro59906 (p : Pattern) (ha : d23609 p = 1) (hb : d208035 p = 1) : d209898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23559 q = 1) (hb : d208035 q = 1) : d209876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23559, d209876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59905 q ha hb
    | true =>
      simp only [d23559, d209876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23560 q = 1) (hb : d208035 q = 1) : d209877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23560, d209877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23560, d209877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23606 q = 1) (hb : d208035 q = 1) : d209895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23606, d209895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23606, d209895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23607 q = 1) (hb : d208035 q = 1) : d209896 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23607, d209896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23607, d209896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23608 q = 1) (hb : d208035 q = 1) : d209897 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23608, d209897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23608, d209897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23609 q = 1) (hb : d208035 q = 1) : d209898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23609, d209898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23609, d209898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59907 (p : Pattern) (ha : d23615 p = 1) (hb : d208035 p = 1) : d209904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23610 q = 1) (hb : d208035 q = 1) : d209899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23610, d209899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59906 q ha hb
    | true =>
      simp only [d23610, d209899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23611 q = 1) (hb : d208035 q = 1) : d209900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23611, d209900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23611, d209900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23612 q = 1) (hb : d208035 q = 1) : d209901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23612, d209901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23612, d209901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23613 q = 1) (hb : d208035 q = 1) : d209902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23613, d209902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23613, d209902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23614 q = 1) (hb : d208035 q = 1) : d209903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23614, d209903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23614, d209903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23615 q = 1) (hb : d208035 q = 1) : d209904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23615, d209904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23615, d209904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59908 (p : Pattern) (ha : d23403 p = 1) (hb : d208035 p = 1) : d209767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208035 q = 1) : d209733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59894 q ha hb
    | true =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208035 q = 1) : d209734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208035 q = 1) : d209739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d208035 q = 1) : d209740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d209740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d209740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23402 q = 1) (hb : d208035 q = 1) : d209766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23402, d209766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23402, d209766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23403 q = 1) (hb : d208035 q = 1) : d209767 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23403, d209767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23403, d209767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59909 (p : Pattern) (ha : d23405 p = 1) (hb : d208035 p = 1) : d209769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208035 q = 1) : d209743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d208035 q = 1) : d209744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d209744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d209744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23404 q = 1) (hb : d208035 q = 1) : d209768 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23404, d209768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23404, d209768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23405 q = 1) (hb : d208035 q = 1) : d209769 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23405, d209769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23405, d209769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59910 (p : Pattern) (ha : d23412 p = 1) (hb : d208035 p = 1) : d209776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208035 q = 1) : d209733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59894 q ha hb
    | true =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208035 q = 1) : d209734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208035 q = 1) : d209739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23410 q = 1) (hb : d208035 q = 1) : d209774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23410, d209774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23410, d209774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23411 q = 1) (hb : d208035 q = 1) : d209775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23411, d209775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23411, d209775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23412 q = 1) (hb : d208035 q = 1) : d209776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23412, d209776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23412, d209776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59911 (p : Pattern) (ha : d23415 p = 1) (hb : d208035 p = 1) : d209779 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208035 q = 1) : d209743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23413 q = 1) (hb : d208035 q = 1) : d209777 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23413, d209777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23413, d209777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23414 q = 1) (hb : d208035 q = 1) : d209778 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23414, d209778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23414, d209778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23415 q = 1) (hb : d208035 q = 1) : d209779 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23415, d209779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23415, d209779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59912 (p : Pattern) (ha : d23421 p = 1) (hb : d208035 p = 1) : d200751 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d532 q = 1) : d532 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d533 q = 1) (hb : d152852 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d533, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23419 q = 1) (hb : d208034 q = 1) : d25781 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d208034, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23419, d208034, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23420 q = 1) (hb : d208034 q = 1) : d25782 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23420, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d23229 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23421 q = 1) (hb : d208035 q = 1) : d200751 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23421, d208035, d200751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23421, d208035, d200751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59913 (p : Pattern) (ha : d23427 p = 1) (hb : d208035 p = 1) : d209783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23422 q = 1) (hb : d208035 q = 1) : d200752 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59912 q ha hb
    | true =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23423 q = 1) (hb : d208035 q = 1) : d200753 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23424 q = 1) (hb : d208035 q = 1) : d200754 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23425 q = 1) (hb : d208035 q = 1) : d200755 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23425, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23231 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
    | true =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23232 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23233 q = 1) (hb : d208035 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23234 q = 1) (hb : d208035 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23234, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23426 q = 1) (hb : d208035 q = 1) : d200756 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23426, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59857 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d208035 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d208035 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23235 q = 1) (hb : d208035 q = 1) : d200528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23235, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23235, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23427 q = 1) (hb : d208035 q = 1) : d209783 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23427, d209783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23427, d209783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59914 (p : Pattern) (ha : d23433 p = 1) (hb : d208035 p = 1) : d209789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23428 q = 1) (hb : d208035 q = 1) : d209784 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23428, d209784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59913 q ha hb
    | true =>
      simp only [d23428, d209784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59876 q ha hb
  have h2 (q : Pattern) (ha : d23429 q = 1) (hb : d208035 q = 1) : d209785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23429, d209785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23429, d209785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23430 q = 1) (hb : d208035 q = 1) : d209786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23430, d209786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23430, d209786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23237 q = 1) (hb : d208035 q = 1) : d209636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23237, d209636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59876 q ha hb
    | true =>
      simp only [d23237, d209636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59858 q ha hb
  have h5 (q : Pattern) (ha : d23238 q = 1) (hb : d208035 q = 1) : d209637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23238, d209637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23238, d209637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23239 q = 1) (hb : d208035 q = 1) : d209638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23239, d209638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23239, d209638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23431 q = 1) (hb : d208035 q = 1) : d209787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23431, d209787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23431, d209787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30 q = 1) (hb : d208035 q = 1) : d30 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23135 q = 1) (hb : d208035 q = 1) : d209542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23135, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59858 q ha hb
    | true =>
      simp only [d23135, d209542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23136 q = 1) (hb : d208035 q = 1) : d209543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23136, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23136, d209543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23137 q = 1) (hb : d208035 q = 1) : d209544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23137, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23137, d209544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23240 q = 1) (hb : d208035 q = 1) : d209639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23240, d209639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23240, d209639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23432 q = 1) (hb : d208035 q = 1) : d209788 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23432, d209788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23432, d209788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23433 q = 1) (hb : d208035 q = 1) : d209789 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23433, d209789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23433, d209789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro59915 (p : Pattern) (ha : d23439 p = 1) (hb : d208035 p = 1) : d209795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23434 q = 1) (hb : d208035 q = 1) : d209790 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23434, d209790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59914 q ha hb
    | true =>
      simp only [d23434, d209790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23435 q = 1) (hb : d208035 q = 1) : d209791 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23435, d209791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23435, d209791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23369 q = 1) (hb : d208035 q = 1) : d209733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59894 q ha hb
    | true =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23370 q = 1) (hb : d208035 q = 1) : d209734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23436 q = 1) (hb : d208035 q = 1) : d209792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23436, d209792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23436, d209792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23437 q = 1) (hb : d208035 q = 1) : d209793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23437, d209793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23437, d209793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23438 q = 1) (hb : d208035 q = 1) : d209794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23438, d209794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23438, d209794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23439 q = 1) (hb : d208035 q = 1) : d209795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23439, d209795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23439, d209795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59916 (p : Pattern) (ha : d23476 p = 1) (hb : d208035 p = 1) : d209801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208035 q = 1) : d209733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59894 q ha hb
    | true =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208035 q = 1) : d209734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23473 q = 1) (hb : d208035 q = 1) : d209798 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23473, d209798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23473, d209798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23474 q = 1) (hb : d208035 q = 1) : d209799 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23474, d209799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23474, d209799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23475 q = 1) (hb : d208035 q = 1) : d209800 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23475, d209800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23475, d209800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23476 q = 1) (hb : d208035 q = 1) : d209801 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23476, d209801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23476, d209801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59917 (p : Pattern) (ha : d208035 p = 1) (hb : d211163 p = 1) : d209807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23406 q = 1) (hb : d208035 q = 1) : d209770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23406, d209770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59908 q ha hb
    | true =>
      simp only [d23406, d209770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59909 q ha hb
  have h2 (q : Pattern) (ha : d23407 q = 1) (hb : d208035 q = 1) : d209771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23407, d209771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23407, d209771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23408 q = 1) (hb : d208035 q = 1) : d209772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23408, d209772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23408, d209772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23409 q = 1) (hb : d208035 q = 1) : d209773 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23409, d209773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23409, d209773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23416 q = 1) (hb : d208035 q = 1) : d209780 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23416, d209780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59910 q ha hb
    | true =>
      simp only [d23416, d209780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59911 q ha hb
  have h6 (q : Pattern) (ha : d23417 q = 1) (hb : d208035 q = 1) : d209781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23417, d209781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23417, d209781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23418 q = 1) (hb : d208035 q = 1) : d209782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23418, d209782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23418, d209782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23440 q = 1) (hb : d208035 q = 1) : d209796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23440, d209796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59915 q ha hb
    | true =>
      simp only [d23440, d209796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59896 q ha hb
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d211159 q = 1) : d209797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211159, d209797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211159, d209797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d23477 q = 1) (hb : d208035 q = 1) : d209802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23477, d209802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59916 q ha hb
    | true =>
      simp only [d23477, d209802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23478 q = 1) (hb : d208035 q = 1) : d209803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23478, d209803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23478, d209803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208035 q = 1) (hb : d211160 q = 1) : d209804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211160, d209804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211160, d209804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208035 q = 1) (hb : d211161 q = 1) : d209805 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211161, d209805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211161, d209805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d211162 q = 1) : d209806 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211162, d209806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211162, d209806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d211163 q = 1) : d209807 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211163, d209807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211163, d209807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59918 (p : Pattern) (ha : d23483 p = 1) (hb : d208035 p = 1) : d209808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208035 q = 1) : d209733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59894 q ha hb
    | true =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208035 q = 1) : d209734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208035 q = 1) : d209739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23376 q = 1) (hb : d208035 q = 1) : d209740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23376, d209740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23376, d209740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23402 q = 1) (hb : d208035 q = 1) : d209766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23402, d209766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23402, d209766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23483 q = 1) (hb : d208035 q = 1) : d209808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23483, d209808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23483, d209808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59919 (p : Pattern) (ha : d23484 p = 1) (hb : d208035 p = 1) : d209809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208035 q = 1) : d209743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23380 q = 1) (hb : d208035 q = 1) : d209744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23380, d209744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23380, d209744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23404 q = 1) (hb : d208035 q = 1) : d209768 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23404, d209768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23404, d209768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23484 q = 1) (hb : d208035 q = 1) : d209809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23484, d209809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23484, d209809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59920 (p : Pattern) (ha : d23489 p = 1) (hb : d208035 p = 1) : d209814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208035 q = 1) : d209733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59894 q ha hb
    | true =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208035 q = 1) : d209734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23375 q = 1) (hb : d208035 q = 1) : d209739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23375, d209739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23410 q = 1) (hb : d208035 q = 1) : d209774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23410, d209774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23410, d209774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23411 q = 1) (hb : d208035 q = 1) : d209775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23411, d209775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23411, d209775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23489 q = 1) (hb : d208035 q = 1) : d209814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23489, d209814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23489, d209814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59921 (p : Pattern) (ha : d23490 p = 1) (hb : d208035 p = 1) : d209815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23373 q = 1) (hb : d208035 q = 1) : d209737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59895 q ha hb
    | true =>
      simp only [d23373, d209737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23374 q = 1) (hb : d208035 q = 1) : d209738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23374, d209738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23379 q = 1) (hb : d208035 q = 1) : d209743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23379, d209743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23413 q = 1) (hb : d208035 q = 1) : d209777 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23413, d209777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23413, d209777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23414 q = 1) (hb : d208035 q = 1) : d209778 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23414, d209778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23414, d209778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23490 q = 1) (hb : d208035 q = 1) : d209815 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23490, d209815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23490, d209815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59922 (p : Pattern) (ha : d23494 p = 1) (hb : d208035 p = 1) : d209819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23434 q = 1) (hb : d208035 q = 1) : d209790 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23434, d209790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59914 q ha hb
    | true =>
      simp only [d23434, d209790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23435 q = 1) (hb : d208035 q = 1) : d209791 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23435, d209791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23435, d209791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23369 q = 1) (hb : d208035 q = 1) : d209733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59894 q ha hb
    | true =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23370 q = 1) (hb : d208035 q = 1) : d209734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23436 q = 1) (hb : d208035 q = 1) : d209792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23436, d209792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23436, d209792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23437 q = 1) (hb : d208035 q = 1) : d209793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23437, d209793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23437, d209793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23438 q = 1) (hb : d208035 q = 1) : d209794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23438, d209794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23438, d209794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23494 q = 1) (hb : d208035 q = 1) : d209819 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23494, d209819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23494, d209819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59923 (p : Pattern) (ha : d23500 p = 1) (hb : d208035 p = 1) : d209822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23369 q = 1) (hb : d208035 q = 1) : d209733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59894 q ha hb
    | true =>
      simp only [d23369, d209733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23370 q = 1) (hb : d208035 q = 1) : d209734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23370, d209734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23473 q = 1) (hb : d208035 q = 1) : d209798 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23473, d209798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23473, d209798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23474 q = 1) (hb : d208035 q = 1) : d209799 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23474, d209799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23474, d209799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23475 q = 1) (hb : d208035 q = 1) : d209800 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23475, d209800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23475, d209800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23500 q = 1) (hb : d208035 q = 1) : d209822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23500, d209822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23500, d209822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59924 (p : Pattern) (ha : d208035 p = 1) (hb : d211168 p = 1) : d209828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23406 q = 1) (hb : d208035 q = 1) : d209770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23406, d209770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59908 q ha hb
    | true =>
      simp only [d23406, d209770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59909 q ha hb
  have h2 (q : Pattern) (ha : d23407 q = 1) (hb : d208035 q = 1) : d209771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23407, d209771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23407, d209771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23408 q = 1) (hb : d208035 q = 1) : d209772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23408, d209772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23408, d209772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23409 q = 1) (hb : d208035 q = 1) : d209773 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23409, d209773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23409, d209773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23416 q = 1) (hb : d208035 q = 1) : d209780 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23416, d209780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59910 q ha hb
    | true =>
      simp only [d23416, d209780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59911 q ha hb
  have h6 (q : Pattern) (ha : d23417 q = 1) (hb : d208035 q = 1) : d209781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23417, d209781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23417, d209781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23418 q = 1) (hb : d208035 q = 1) : d209782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23418, d209782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23418, d209782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23440 q = 1) (hb : d208035 q = 1) : d209796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23440, d209796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59915 q ha hb
    | true =>
      simp only [d23440, d209796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59896 q ha hb
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d211159 q = 1) : d209797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211159, d209797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211159, d209797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d23477 q = 1) (hb : d208035 q = 1) : d209802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23477, d209802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59916 q ha hb
    | true =>
      simp only [d23477, d209802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23478 q = 1) (hb : d208035 q = 1) : d209803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23478, d209803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23478, d209803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208035 q = 1) (hb : d211160 q = 1) : d209804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211160, d209804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211160, d209804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208035 q = 1) (hb : d211161 q = 1) : d209805 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211161, d209805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211161, d209805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d211162 q = 1) : d209806 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211162, d209806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211162, d209806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23485 q = 1) (hb : d208035 q = 1) : d209810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23485, d209810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59918 q ha hb
    | true =>
      simp only [d23485, d209810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59919 q ha hb
  have h16 (q : Pattern) (ha : d23486 q = 1) (hb : d208035 q = 1) : d209811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23486, d209811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23486, d209811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23487 q = 1) (hb : d208035 q = 1) : d209812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23487, d209812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23487, d209812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23488 q = 1) (hb : d208035 q = 1) : d209813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23488, d209813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23488, d209813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23491 q = 1) (hb : d208035 q = 1) : d209816 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23491, d209816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59920 q ha hb
    | true =>
      simp only [d23491, d209816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59921 q ha hb
  have h20 (q : Pattern) (ha : d23492 q = 1) (hb : d208035 q = 1) : d209817 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23492, d209817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23492, d209817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23493 q = 1) (hb : d208035 q = 1) : d209818 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23493, d209818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d23493, d209818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d23495 q = 1) (hb : d208035 q = 1) : d209820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23495, d209820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59922 q ha hb
    | true =>
      simp only [d23495, d209820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59899 q ha hb
  have h23 (q : Pattern) (ha : d208035 q = 1) (hb : d211164 q = 1) : d209821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211164, d209821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d211164, d209821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d23501 q = 1) (hb : d208035 q = 1) : d209823 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23501, d209823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59923 q ha hb
    | true =>
      simp only [d23501, d209823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d23502 q = 1) (hb : d208035 q = 1) : d209824 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23502, d209824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23502, d209824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d208035 q = 1) (hb : d211165 q = 1) : d209825 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211165, d209825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d211165, d209825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d208035 q = 1) (hb : d211166 q = 1) : d209826 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211166, d209826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d211166, d209826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d208035 q = 1) (hb : d211167 q = 1) : d209827 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211167, d209827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d211167, d209827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d208035 q = 1) (hb : d211168 q = 1) : d209828 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211168, d209828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211168, d209828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro59925 (p : Pattern) (ha : d208035 p = 1) (hb : d211175 p = 1) : d209848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23495 q = 1) (hb : d208035 q = 1) : d209820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23495, d209820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59922 q ha hb
    | true =>
      simp only [d23495, d209820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59899 q ha hb
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d211164 q = 1) : d209821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211164, d209821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211164, d209821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23501 q = 1) (hb : d208035 q = 1) : d209823 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23501, d209823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59923 q ha hb
    | true =>
      simp only [d23501, d209823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23502 q = 1) (hb : d208035 q = 1) : d209824 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23502, d209824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23502, d209824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211165 q = 1) : d209825 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211165, d209825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211165, d209825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211173 q = 1) : d209846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211173, d209846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211173, d209846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211174 q = 1) : d209847 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211174, d209847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211174, d209847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211175 q = 1) : d209848 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211175, d209848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211175, d209848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59926 (p : Pattern) (ha : d23539 p = 1) (hb : d208035 p = 1) : d209856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23534 q = 1) (hb : d208035 q = 1) : d200839 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d200839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d200839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59912 q ha hb
  have h2 (q : Pattern) (ha : d23422 q = 1) (hb : d208035 q = 1) : d200752 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59912 q ha hb
    | true =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23535 q = 1) (hb : d208035 q = 1) : d200840 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d200840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23535, d200840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23423 q = 1) (hb : d208035 q = 1) : d200753 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23536 q = 1) (hb : d208035 q = 1) : d200841 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d200841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23536, d200841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23537 q = 1) (hb : d208035 q = 1) : d200842 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d200842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23537, d200842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23310 q = 1) (hb : d208035 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
  have h8 (q : Pattern) (ha : d23231 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
    | true =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23311 q = 1) (hb : d208035 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23311, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23232 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23312 q = 1) (hb : d208035 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23312, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23313 q = 1) (hb : d208035 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23313, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23538 q = 1) (hb : d208035 q = 1) : d200843 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d200843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23538, d200843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d208035 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59857 q ha hb
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59857 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12600 q = 1) (hb : d208035 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9384 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12601 q = 1) (hb : d208035 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12602 q = 1) (hb : d208035 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23314 q = 1) (hb : d208035 q = 1) : d200615 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23314, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23314, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23539 q = 1) (hb : d208035 q = 1) : d209856 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23539, d209856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23539, d209856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro59927 (p : Pattern) (ha : d23545 p = 1) (hb : d208035 p = 1) : d209862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23540 q = 1) (hb : d208035 q = 1) : d209857 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23540, d209857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59926 q ha hb
    | true =>
      simp only [d23540, d209857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59887 q ha hb
  have h2 (q : Pattern) (ha : d23541 q = 1) (hb : d208035 q = 1) : d209858 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23541, d209858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23541, d209858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23542 q = 1) (hb : d208035 q = 1) : d209859 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23542, d209859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23542, d209859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23316 q = 1) (hb : d208035 q = 1) : d209694 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23316, d209694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59887 q ha hb
    | true =>
      simp only [d23316, d209694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59865 q ha hb
  have h5 (q : Pattern) (ha : d23317 q = 1) (hb : d208035 q = 1) : d209695 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23317, d209695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23317, d209695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23318 q = 1) (hb : d208035 q = 1) : d209696 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23318, d209696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23318, d209696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23543 q = 1) (hb : d208035 q = 1) : d209860 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23543, d209860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23543, d209860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d208035 q = 1) : d71 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23172 q = 1) (hb : d208035 q = 1) : d209579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59865 q ha hb
    | true =>
      simp only [d23172, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23173 q = 1) (hb : d208035 q = 1) : d209580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23174 q = 1) (hb : d208035 q = 1) : d209581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23319 q = 1) (hb : d208035 q = 1) : d209697 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23319, d209697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23319, d209697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23544 q = 1) (hb : d208035 q = 1) : d209861 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23544, d209861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23544, d209861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23545 q = 1) (hb : d208035 q = 1) : d209862 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23545, d209862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23545, d209862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro59928 (p : Pattern) (ha : d23550 p = 1) (hb : d208035 p = 1) : d209867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23316 q = 1) (hb : d208035 q = 1) : d209694 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23316, d209694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59887 q ha hb
    | true =>
      simp only [d23316, d209694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59865 q ha hb
  have h2 (q : Pattern) (ha : d23317 q = 1) (hb : d208035 q = 1) : d209695 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23317, d209695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23317, d209695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23318 q = 1) (hb : d208035 q = 1) : d209696 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23318, d209696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23318, d209696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d208035 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23172 q = 1) (hb : d208035 q = 1) : d209579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23172, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59865 q ha hb
    | true =>
      simp only [d23172, d209579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23173 q = 1) (hb : d208035 q = 1) : d209580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23173, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23173, d209580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23174 q = 1) (hb : d208035 q = 1) : d209581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23174, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23174, d209581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23319 q = 1) (hb : d208035 q = 1) : d209697 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23319, d209697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23319, d209697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23548 q = 1) (hb : d208035 q = 1) : d209865 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23548, d209865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23548, d209865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23549 q = 1) (hb : d208035 q = 1) : d209866 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23549, d209866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23549, d209866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23550 q = 1) (hb : d208035 q = 1) : d209867 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23550, d209867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23550, d209867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro59929 (p : Pattern) (ha : d23556 p = 1) (hb : d208035 p = 1) : d209873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23546 q = 1) (hb : d208035 q = 1) : d209863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23546, d209863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59927 q ha hb
    | true =>
      simp only [d23546, d209863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23547 q = 1) (hb : d208035 q = 1) : d209864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23547, d209864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23547, d209864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23551 q = 1) (hb : d208035 q = 1) : d209868 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23551, d209868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59928 q ha hb
    | true =>
      simp only [d23551, d209868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23552 q = 1) (hb : d208035 q = 1) : d209869 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23552, d209869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23552, d209869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23553 q = 1) (hb : d208035 q = 1) : d209870 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23553, d209870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23553, d209870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23554 q = 1) (hb : d208035 q = 1) : d209871 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23554, d209871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23554, d209871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23555 q = 1) (hb : d208035 q = 1) : d209872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23555, d209872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23555, d209872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23556 q = 1) (hb : d208035 q = 1) : d209873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23556, d209873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23556, d209873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59930 (p : Pattern) (ha : d23564 p = 1) (hb : d208035 p = 1) : d209881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23551 q = 1) (hb : d208035 q = 1) : d209868 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23551, d209868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59928 q ha hb
    | true =>
      simp only [d23551, d209868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23552 q = 1) (hb : d208035 q = 1) : d209869 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23552, d209869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23552, d209869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23559 q = 1) (hb : d208035 q = 1) : d209876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23559, d209876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59905 q ha hb
    | true =>
      simp only [d23559, d209876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23560 q = 1) (hb : d208035 q = 1) : d209877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23560, d209877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23560, d209877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23561 q = 1) (hb : d208035 q = 1) : d209878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23561, d209878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23561, d209878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23562 q = 1) (hb : d208035 q = 1) : d209879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23562, d209879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23562, d209879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23563 q = 1) (hb : d208035 q = 1) : d209880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23563, d209880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23563, d209880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23564 q = 1) (hb : d208035 q = 1) : d209881 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23564, d209881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23564, d209881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59931 (p : Pattern) (ha : d23598 p = 1) (hb : d208035 p = 1) : d209887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23551 q = 1) (hb : d208035 q = 1) : d209868 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23551, d209868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59928 q ha hb
    | true =>
      simp only [d23551, d209868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23552 q = 1) (hb : d208035 q = 1) : d209869 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23552, d209869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23552, d209869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23595 q = 1) (hb : d208035 q = 1) : d209884 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23595, d209884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23595, d209884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23596 q = 1) (hb : d208035 q = 1) : d209885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23596, d209885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23596, d209885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23597 q = 1) (hb : d208035 q = 1) : d209886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23597, d209886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23597, d209886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23598 q = 1) (hb : d208035 q = 1) : d209887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23598, d209887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23598, d209887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59932 (p : Pattern) (ha : d208035 p = 1) (hb : d211185 p = 1) : d209893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23565 q = 1) (hb : d208035 q = 1) : d209882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23565, d209882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59929 q ha hb
    | true =>
      simp only [d23565, d209882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59930 q ha hb
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d211181 q = 1) : d209883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211181, d209883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211181, d209883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23599 q = 1) (hb : d208035 q = 1) : d209888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23599, d209888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59931 q ha hb
    | true =>
      simp only [d23599, d209888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23600 q = 1) (hb : d208035 q = 1) : d209889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23600, d209889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23600, d209889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211182 q = 1) : d209890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211182, d209890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211182, d209890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211183 q = 1) : d209891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211183, d209891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211183, d209891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211184 q = 1) : d209892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211184, d209892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211184, d209892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211185 q = 1) : d209893 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211185, d209893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211185, d209893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59933 (p : Pattern) (ha : d208035 p = 1) (hb : d211191 p = 1) : d209910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23389 q = 1) (hb : d208035 q = 1) : d209753 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23389, d209753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23389, d209753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59898 q ha hb
  have h2 (q : Pattern) (ha : d23390 q = 1) (hb : d208035 q = 1) : d209754 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23390, d209754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23390, d209754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23399 q = 1) (hb : d208035 q = 1) : d209763 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23399, d209763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59898 q ha hb
    | true =>
      simp only [d23399, d209763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59901 q ha hb
  have h4 (q : Pattern) (ha : d23400 q = 1) (hb : d208035 q = 1) : d209764 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23400, d209764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23400, d209764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23401 q = 1) (hb : d208035 q = 1) : d209765 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d23401, d209765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23401, d209765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211169 q = 1) : d209829 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211169, d209829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59917 q ha hb
    | true =>
      simp only [d211169, d209829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59924 q ha hb
  have h7 (q : Pattern) (ha : d23520 q = 1) (hb : d208035 q = 1) : d209842 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23520, d209842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59902 q ha hb
    | true =>
      simp only [d23520, d209842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59903 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211170 q = 1) : d209843 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211170, d209843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211170, d209843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d211171 q = 1) : d209844 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211171, d209844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211171, d209844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d208035 q = 1) (hb : d211172 q = 1) : d209845 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211172, d209845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211172, d209845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208035 q = 1) (hb : d211176 q = 1) : d209849 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211176, d209849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211176, d209849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59925 q ha hb
  have h12 (q : Pattern) (ha : d23529 q = 1) (hb : d208035 q = 1) : d209851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23529, d209851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23529, d209851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59904 q ha hb
  have h13 (q : Pattern) (ha : d208035 q = 1) (hb : d211177 q = 1) : d209852 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211177, d209852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211177, d209852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d211178 q = 1) : d209853 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211178, d209853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211178, d209853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d211179 q = 1) : d209854 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211179, d209854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211179, d209854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d208035 q = 1) (hb : d211180 q = 1) : d209855 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211180, d209855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211180, d209855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208035 q = 1) (hb : d211186 q = 1) : d209894 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211186, d209894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211186, d209894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59932 q ha hb
  have h18 (q : Pattern) (ha : d23616 q = 1) (hb : d208035 q = 1) : d209905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23616, d209905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23616, d209905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59907 q ha hb
  have h19 (q : Pattern) (ha : d208035 q = 1) (hb : d211187 q = 1) : d209906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211187, d209906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211187, d209906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d208035 q = 1) (hb : d211188 q = 1) : d209907 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211188, d209907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d211188, d209907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d208035 q = 1) (hb : d211189 q = 1) : d209908 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211189, d209908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d211189, d209908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d208035 q = 1) (hb : d211190 q = 1) : d209909 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211190, d209909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211190, d209909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d208035 q = 1) (hb : d211191 q = 1) : d209910 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211191, d209910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211191, d209910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro59934 (p : Pattern) (ha : d208035 p = 1) (hb : d211197 p = 1) : d209916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d211192 q = 1) : d209911 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211192, d209911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211192, d209911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59933 q ha hb
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d211193 q = 1) : d209912 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211193, d209912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211193, d209912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d211194 q = 1) : d209913 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211194, d209913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211194, d209913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d211195 q = 1) : d209914 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211195, d209914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211195, d209914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211196 q = 1) : d209915 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211196, d209915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211196, d209915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211197 q = 1) : d209916 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211197, d209916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211197, d209916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59935 (p : Pattern) (ha : d5457 p = 1) (hb : d208035 p = 1) : d209923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5451 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50483 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5452 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5453 q = 1) (hb : d208035 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5454 q = 1) (hb : d208035 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5455 q = 1) (hb : d208035 q = 1) : d209918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5455, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5457 q = 1) (hb : d208035 q = 1) : d209923 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5457, d209923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5457, d209923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59936 (p : Pattern) (ha : d23630 p = 1) (hb : d208035 p = 1) : d209783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23422 q = 1) (hb : d208035 q = 1) : d200752 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59912 q ha hb
    | true =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23423 q = 1) (hb : d208035 q = 1) : d200753 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23424 q = 1) (hb : d208035 q = 1) : d200754 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23425 q = 1) (hb : d208035 q = 1) : d200755 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23425, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23231 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
    | true =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23232 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23233 q = 1) (hb : d208035 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23234 q = 1) (hb : d208035 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23234, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23426 q = 1) (hb : d208035 q = 1) : d200756 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23426, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h14 (q : Pattern) (ha : d23629 q = 1) (hb : d208035 q = 1) : d200528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23629, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23629, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23630 q = 1) (hb : d208035 q = 1) : d209783 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23630, d209783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23630, d209783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59937 (p : Pattern) (ha : d23631 p = 1) (hb : d208035 p = 1) : d209919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23231 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
    | true =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23232 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23233 q = 1) (hb : d208035 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23234 q = 1) (hb : d208035 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23234, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5451 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50483 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5452 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5453 q = 1) (hb : d208035 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5454 q = 1) (hb : d208035 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5454, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23629 q = 1) (hb : d208035 q = 1) : d200528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23629, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23629, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5455 q = 1) (hb : d208035 q = 1) : d209918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5455, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23631 q = 1) (hb : d208035 q = 1) : d209919 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23631, d209919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23631, d209919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59938 (p : Pattern) (ha : d23641 p = 1) (hb : d208035 p = 1) : d209930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23632 q = 1) (hb : d208035 q = 1) : d209920 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23632, d209920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59936 q ha hb
    | true =>
      simp only [d23632, d209920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59937 q ha hb
  have h2 (q : Pattern) (ha : d23633 q = 1) (hb : d208035 q = 1) : d209921 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23633, d209921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23633, d209921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23634 q = 1) (hb : d208035 q = 1) : d209922 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23634, d209922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23634, d209922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23635 q = 1) (hb : d208035 q = 1) : d209924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23635, d209924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59937 q ha hb
    | true =>
      simp only [d23635, d209924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59935 q ha hb
  have h5 (q : Pattern) (ha : d23636 q = 1) (hb : d208035 q = 1) : d209925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23636, d209925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23636, d209925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23637 q = 1) (hb : d208035 q = 1) : d209926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23637, d209926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23637, d209926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23638 q = 1) (hb : d208035 q = 1) : d209927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23638, d209927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23638, d209927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23639 q = 1) (hb : d208035 q = 1) : d209928 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23639, d209928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23639, d209928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23640 q = 1) (hb : d208035 q = 1) : d209929 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23640, d209929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23640, d209929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23641 q = 1) (hb : d208035 q = 1) : d209930 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23641, d209930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23641, d209930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro59939 (p : Pattern) (ha : d23645 p = 1) (hb : d208035 p = 1) : d209934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23635 q = 1) (hb : d208035 q = 1) : d209924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23635, d209924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59937 q ha hb
    | true =>
      simp only [d23635, d209924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59935 q ha hb
  have h2 (q : Pattern) (ha : d23636 q = 1) (hb : d208035 q = 1) : d209925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23636, d209925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23636, d209925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23637 q = 1) (hb : d208035 q = 1) : d209926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23637, d209926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23637, d209926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23639 q = 1) (hb : d208035 q = 1) : d209928 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23639, d209928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23639, d209928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23644 q = 1) (hb : d208035 q = 1) : d209933 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23644, d209933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23644, d209933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23645 q = 1) (hb : d208035 q = 1) : d209934 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23645, d209934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23645, d209934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59940 (p : Pattern) (ha : d23651 p = 1) (hb : d208035 p = 1) : d209940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208035 q = 1) : d209931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59938 q ha hb
    | true =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208035 q = 1) : d209932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208035 q = 1) : d209937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d208035 q = 1) : d209938 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d209938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d209938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23650 q = 1) (hb : d208035 q = 1) : d209939 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23650, d209939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23650, d209939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23651 q = 1) (hb : d208035 q = 1) : d209940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23651, d209940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23651, d209940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59941 (p : Pattern) (ha : d23655 p = 1) (hb : d208035 p = 1) : d209944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208035 q = 1) : d209941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d208035 q = 1) : d209942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d209942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d209942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23654 q = 1) (hb : d208035 q = 1) : d209943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23654, d209943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23654, d209943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23655 q = 1) (hb : d208035 q = 1) : d209944 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23655, d209944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23655, d209944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59942 (p : Pattern) (ha : d23661 p = 1) (hb : d208035 p = 1) : d209950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23656 q = 1) (hb : d208035 q = 1) : d209945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59940 q ha hb
    | true =>
      simp only [d23656, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59941 q ha hb
  have h2 (q : Pattern) (ha : d23657 q = 1) (hb : d208035 q = 1) : d209946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23657, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23658 q = 1) (hb : d208035 q = 1) : d209947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23658, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23659 q = 1) (hb : d208035 q = 1) : d209948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23659, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23660 q = 1) (hb : d208035 q = 1) : d209949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23661 q = 1) (hb : d208035 q = 1) : d209950 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23661, d209950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23661, d209950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59943 (p : Pattern) (ha : d23664 p = 1) (hb : d208035 p = 1) : d209953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208035 q = 1) : d209931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59938 q ha hb
    | true =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208035 q = 1) : d209932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208035 q = 1) : d209937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d208035 q = 1) : d209938 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d209938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d209938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23650 q = 1) (hb : d208035 q = 1) : d209939 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23650, d209939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23650, d209939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23664 q = 1) (hb : d208035 q = 1) : d209953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23664, d209953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23664, d209953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59944 (p : Pattern) (ha : d23665 p = 1) (hb : d208035 p = 1) : d209954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208035 q = 1) : d209941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d208035 q = 1) : d209942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d209942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d209942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23654 q = 1) (hb : d208035 q = 1) : d209943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23654, d209943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23654, d209943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23665 q = 1) (hb : d208035 q = 1) : d209954 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23665, d209954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23665, d209954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59945 (p : Pattern) (ha : d23671 p = 1) (hb : d208035 p = 1) : d209960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23656 q = 1) (hb : d208035 q = 1) : d209945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59940 q ha hb
    | true =>
      simp only [d23656, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59941 q ha hb
  have h2 (q : Pattern) (ha : d23657 q = 1) (hb : d208035 q = 1) : d209946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23657, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23658 q = 1) (hb : d208035 q = 1) : d209947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23658, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23659 q = 1) (hb : d208035 q = 1) : d209948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23659, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23660 q = 1) (hb : d208035 q = 1) : d209949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23666 q = 1) (hb : d208035 q = 1) : d209955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23666, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59943 q ha hb
    | true =>
      simp only [d23666, d209955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59944 q ha hb
  have h7 (q : Pattern) (ha : d23667 q = 1) (hb : d208035 q = 1) : d209956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23667, d209956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23668 q = 1) (hb : d208035 q = 1) : d209957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23668, d209957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23669 q = 1) (hb : d208035 q = 1) : d209958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23669, d209958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23670 q = 1) (hb : d208035 q = 1) : d209959 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23670, d209959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23671 q = 1) (hb : d208035 q = 1) : d209960 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23671, d209960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23671, d209960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59946 (p : Pattern) (ha : d23793 p = 1) (hb : d208035 p = 1) : d210034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23656 q = 1) (hb : d208035 q = 1) : d209945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59940 q ha hb
    | true =>
      simp only [d23656, d209945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59941 q ha hb
  have h2 (q : Pattern) (ha : d23657 q = 1) (hb : d208035 q = 1) : d209946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23657, d209946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23658 q = 1) (hb : d208035 q = 1) : d209947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23658, d209947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23659 q = 1) (hb : d208035 q = 1) : d209948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23659, d209948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23660 q = 1) (hb : d208035 q = 1) : d209949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d209949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23788 q = 1) (hb : d208035 q = 1) : d210029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23788, d210029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59941 q ha hb
    | true =>
      simp only [d23788, d210029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23789 q = 1) (hb : d208035 q = 1) : d210030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23789, d210030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23789, d210030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23790 q = 1) (hb : d208035 q = 1) : d210031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23790, d210031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23790, d210031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23791 q = 1) (hb : d208035 q = 1) : d210032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23791, d210032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23791, d210032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23792 q = 1) (hb : d208035 q = 1) : d210033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23792, d210033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23792, d210033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23793 q = 1) (hb : d208035 q = 1) : d210034 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23793, d210034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23793, d210034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59947 (p : Pattern) (ha : d23799 p = 1) (hb : d208035 p = 1) : d210040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23788 q = 1) (hb : d208035 q = 1) : d210029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23788, d210029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59941 q ha hb
    | true =>
      simp only [d23788, d210029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23789 q = 1) (hb : d208035 q = 1) : d210030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23789, d210030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23789, d210030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23790 q = 1) (hb : d208035 q = 1) : d210031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23790, d210031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23790, d210031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23791 q = 1) (hb : d208035 q = 1) : d210032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23791, d210032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23791, d210032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23792 q = 1) (hb : d208035 q = 1) : d210033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23792, d210033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23792, d210033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23794 q = 1) (hb : d208035 q = 1) : d210035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23794, d210035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59944 q ha hb
    | true =>
      simp only [d23794, d210035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23795 q = 1) (hb : d208035 q = 1) : d210036 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23795, d210036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23795, d210036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23796 q = 1) (hb : d208035 q = 1) : d210037 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23796, d210037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23796, d210037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23797 q = 1) (hb : d208035 q = 1) : d210038 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23797, d210038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23797, d210038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23798 q = 1) (hb : d208035 q = 1) : d210039 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23798, d210039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23798, d210039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23799 q = 1) (hb : d208035 q = 1) : d210040 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23799, d210040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23799, d210040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59948 (p : Pattern) (ha : d23808 p = 1) (hb : d208035 p = 1) : d210049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23794 q = 1) (hb : d208035 q = 1) : d210035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23794, d210035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59944 q ha hb
    | true =>
      simp only [d23794, d210035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23795 q = 1) (hb : d208035 q = 1) : d210036 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23795, d210036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23795, d210036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23796 q = 1) (hb : d208035 q = 1) : d210037 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23796, d210037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23796, d210037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23797 q = 1) (hb : d208035 q = 1) : d210038 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23797, d210038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23797, d210038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23798 q = 1) (hb : d208035 q = 1) : d210039 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23798, d210039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23798, d210039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23808 q = 1) (hb : d208035 q = 1) : d210049 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23808, d210049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23808, d210049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59949 (p : Pattern) (ha : d5501 p = 1) (hb : d208035 p = 1) : d210066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5495 q = 1) (hb : d208035 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50483 q ha hb
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50483 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5496 q = 1) (hb : d208035 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5452 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5497 q = 1) (hb : d208035 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5498 q = 1) (hb : d208035 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5499 q = 1) (hb : d208035 q = 1) : d210060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5499, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5501 q = 1) (hb : d208035 q = 1) : d210066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5501, d210066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5501, d210066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59950 (p : Pattern) (ha : d23825 p = 1) (hb : d208035 p = 1) : d210061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23310 q = 1) (hb : d208035 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
  have h2 (q : Pattern) (ha : d23231 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
    | true =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23311 q = 1) (hb : d208035 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23311, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23232 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23312 q = 1) (hb : d208035 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23312, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23313 q = 1) (hb : d208035 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23313, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5495 q = 1) (hb : d208035 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50483 q ha hb
  have h8 (q : Pattern) (ha : d5451 q = 1) (hb : d208035 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50483 q ha hb
    | true =>
      simp only [d5451, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5496 q = 1) (hb : d208035 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5496, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5452 q = 1) (hb : d208035 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5452, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5497 q = 1) (hb : d208035 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5497, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5498 q = 1) (hb : d208035 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5498, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23820 q = 1) (hb : d208035 q = 1) : d200615 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23820, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23820, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5499 q = 1) (hb : d208035 q = 1) : d210060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5499, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d23825 q = 1) (hb : d208035 q = 1) : d210061 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23825, d210061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23825, d210061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59951 (p : Pattern) (ha : d23848 p = 1) (hb : d208035 p = 1) : d210085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23830 q = 1) (hb : d208035 q = 1) : d210067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23830, d210067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59950 q ha hb
    | true =>
      simp only [d23830, d210067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59949 q ha hb
  have h2 (q : Pattern) (ha : d23831 q = 1) (hb : d208035 q = 1) : d210068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23831, d210068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23831, d210068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23832 q = 1) (hb : d208035 q = 1) : d210069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23832, d210069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23832, d210069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23838 q = 1) (hb : d208035 q = 1) : d210075 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23838, d210075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23838, d210075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23847 q = 1) (hb : d208035 q = 1) : d210084 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23847, d210084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23847, d210084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23848 q = 1) (hb : d208035 q = 1) : d210085 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23848, d210085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23848, d210085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59952 (p : Pattern) (ha : d23906 p = 1) (hb : d208035 p = 1) : d210108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23849 q = 1) (hb : d208035 q = 1) : d210086 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23849, d210086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59951 q ha hb
    | true =>
      simp only [d23849, d210086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23850 q = 1) (hb : d208035 q = 1) : d210087 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23850, d210087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23850, d210087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23903 q = 1) (hb : d208035 q = 1) : d210105 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23903, d210105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23903, d210105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23904 q = 1) (hb : d208035 q = 1) : d210106 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23904, d210106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23904, d210106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23905 q = 1) (hb : d208035 q = 1) : d210107 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23905, d210107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23905, d210107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23906 q = 1) (hb : d208035 q = 1) : d210108 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23906, d210108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23906, d210108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59953 (p : Pattern) (ha : d23912 p = 1) (hb : d208035 p = 1) : d210114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23907 q = 1) (hb : d208035 q = 1) : d210109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23907, d210109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59952 q ha hb
    | true =>
      simp only [d23907, d210109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23908 q = 1) (hb : d208035 q = 1) : d210110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23908, d210110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23908, d210110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23909 q = 1) (hb : d208035 q = 1) : d210111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23909, d210111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23909, d210111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23910 q = 1) (hb : d208035 q = 1) : d210112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23910, d210112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23910, d210112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23911 q = 1) (hb : d208035 q = 1) : d210113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23911, d210113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23911, d210113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23912 q = 1) (hb : d208035 q = 1) : d210114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23912, d210114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23912, d210114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59954 (p : Pattern) (ha : d23676 p = 1) (hb : d208035 p = 1) : d209965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208035 q = 1) : d209931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59938 q ha hb
    | true =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208035 q = 1) : d209932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208035 q = 1) : d209937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d208035 q = 1) : d209938 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d209938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d209938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23675 q = 1) (hb : d208035 q = 1) : d209964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23675, d209964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23675, d209964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23676 q = 1) (hb : d208035 q = 1) : d209965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23676, d209965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23676, d209965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59955 (p : Pattern) (ha : d23678 p = 1) (hb : d208035 p = 1) : d209967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208035 q = 1) : d209941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d208035 q = 1) : d209942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d209942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d209942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23677 q = 1) (hb : d208035 q = 1) : d209966 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23677, d209966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23677, d209966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23678 q = 1) (hb : d208035 q = 1) : d209967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23678, d209967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23678, d209967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59956 (p : Pattern) (ha : d23685 p = 1) (hb : d208035 p = 1) : d209974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208035 q = 1) : d209931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59938 q ha hb
    | true =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208035 q = 1) : d209932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208035 q = 1) : d209937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23683 q = 1) (hb : d208035 q = 1) : d209972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23683, d209972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23683, d209972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23684 q = 1) (hb : d208035 q = 1) : d209973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23684, d209973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23684, d209973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23685 q = 1) (hb : d208035 q = 1) : d209974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23685, d209974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23685, d209974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59957 (p : Pattern) (ha : d23688 p = 1) (hb : d208035 p = 1) : d209977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208035 q = 1) : d209941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23686 q = 1) (hb : d208035 q = 1) : d209975 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23686, d209975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23686, d209975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23687 q = 1) (hb : d208035 q = 1) : d209976 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23687, d209976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23687, d209976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23688 q = 1) (hb : d208035 q = 1) : d209977 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23688, d209977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23688, d209977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59958 (p : Pattern) (ha : d23694 p = 1) (hb : d208035 p = 1) : d21840 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d823 q = 1) : d823 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d532 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d824 q = 1) (hb : d152852 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d824, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23692 q = 1) (hb : d208034 q = 1) : d9760 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23692, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23692, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23693 q = 1) (hb : d208034 q = 1) : d9761 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23693, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23693, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d23420 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23694 q = 1) (hb : d208035 q = 1) : d21840 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23694, d208035, d21840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23694, d208035, d21840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59959 (p : Pattern) (ha : d23700 p = 1) (hb : d208035 p = 1) : d209982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23695 q = 1) (hb : d208035 q = 1) : d21841 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59958 q ha hb
    | true =>
      simp only [d23695, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23696 q = 1) (hb : d208035 q = 1) : d21842 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23696, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23697 q = 1) (hb : d208035 q = 1) : d21843 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23697, d21843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23697, d21843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23698 q = 1) (hb : d208035 q = 1) : d21844 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23698, d21844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23698, d21844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23422 q = 1) (hb : d208035 q = 1) : d200752 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59912 q ha hb
    | true =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23423 q = 1) (hb : d208035 q = 1) : d200753 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23424 q = 1) (hb : d208035 q = 1) : d200754 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23425 q = 1) (hb : d208035 q = 1) : d200755 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23425, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23699 q = 1) (hb : d208035 q = 1) : d209981 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23699, d209981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23699, d209981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23231 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
    | true =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23232 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23233 q = 1) (hb : d208035 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23234 q = 1) (hb : d208035 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23234, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23426 q = 1) (hb : d208035 q = 1) : d200756 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23426, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23700 q = 1) (hb : d208035 q = 1) : d209982 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23700, d209982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23700, d209982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59960 (p : Pattern) (ha : d23706 p = 1) (hb : d208035 p = 1) : d209988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23701 q = 1) (hb : d208035 q = 1) : d209983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23701, d209983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59959 q ha hb
    | true =>
      simp only [d23701, d209983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59936 q ha hb
  have h2 (q : Pattern) (ha : d23702 q = 1) (hb : d208035 q = 1) : d209984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23702, d209984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23702, d209984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23703 q = 1) (hb : d208035 q = 1) : d209985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23703, d209985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23703, d209985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23632 q = 1) (hb : d208035 q = 1) : d209920 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23632, d209920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59936 q ha hb
    | true =>
      simp only [d23632, d209920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59937 q ha hb
  have h5 (q : Pattern) (ha : d23633 q = 1) (hb : d208035 q = 1) : d209921 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23633, d209921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23633, d209921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23634 q = 1) (hb : d208035 q = 1) : d209922 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23634, d209922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23634, d209922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23704 q = 1) (hb : d208035 q = 1) : d209986 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23704, d209986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23704, d209986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23635 q = 1) (hb : d208035 q = 1) : d209924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23635, d209924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59937 q ha hb
    | true =>
      simp only [d23635, d209924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59935 q ha hb
  have h9 (q : Pattern) (ha : d23636 q = 1) (hb : d208035 q = 1) : d209925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23636, d209925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23636, d209925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23637 q = 1) (hb : d208035 q = 1) : d209926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23637, d209926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23637, d209926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23638 q = 1) (hb : d208035 q = 1) : d209927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23638, d209927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23638, d209927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23705 q = 1) (hb : d208035 q = 1) : d209987 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23705, d209987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23705, d209987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23706 q = 1) (hb : d208035 q = 1) : d209988 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23706, d209988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23706, d209988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro59961 (p : Pattern) (ha : d23712 p = 1) (hb : d208035 p = 1) : d209994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23707 q = 1) (hb : d208035 q = 1) : d209989 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23707, d209989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59960 q ha hb
    | true =>
      simp only [d23707, d209989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23708 q = 1) (hb : d208035 q = 1) : d209990 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23708, d209990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23708, d209990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23642 q = 1) (hb : d208035 q = 1) : d209931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59938 q ha hb
    | true =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23643 q = 1) (hb : d208035 q = 1) : d209932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23709 q = 1) (hb : d208035 q = 1) : d209991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23709, d209991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23709, d209991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23710 q = 1) (hb : d208035 q = 1) : d209992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23710, d209992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23710, d209992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23711 q = 1) (hb : d208035 q = 1) : d209993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23711, d209993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23711, d209993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23712 q = 1) (hb : d208035 q = 1) : d209994 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23712, d209994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23712, d209994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59962 (p : Pattern) (ha : d23756 p = 1) (hb : d208035 p = 1) : d210000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208035 q = 1) : d209931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59938 q ha hb
    | true =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208035 q = 1) : d209932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23753 q = 1) (hb : d208035 q = 1) : d209997 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23753, d209997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23753, d209997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23754 q = 1) (hb : d208035 q = 1) : d209998 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23754, d209998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23754, d209998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23755 q = 1) (hb : d208035 q = 1) : d209999 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23755, d209999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23755, d209999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23756 q = 1) (hb : d208035 q = 1) : d210000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23756, d210000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23756, d210000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59963 (p : Pattern) (ha : d208035 p = 1) (hb : d211203 p = 1) : d210006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23679 q = 1) (hb : d208035 q = 1) : d209968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23679, d209968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59954 q ha hb
    | true =>
      simp only [d23679, d209968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59955 q ha hb
  have h2 (q : Pattern) (ha : d23680 q = 1) (hb : d208035 q = 1) : d209969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23680, d209969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23680, d209969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23681 q = 1) (hb : d208035 q = 1) : d209970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23681, d209970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23681, d209970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23682 q = 1) (hb : d208035 q = 1) : d209971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23682, d209971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23682, d209971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23689 q = 1) (hb : d208035 q = 1) : d209978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23689, d209978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59956 q ha hb
    | true =>
      simp only [d23689, d209978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59957 q ha hb
  have h6 (q : Pattern) (ha : d23690 q = 1) (hb : d208035 q = 1) : d209979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23690, d209979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23690, d209979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23691 q = 1) (hb : d208035 q = 1) : d209980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23691, d209980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23691, d209980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23713 q = 1) (hb : d208035 q = 1) : d209995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23713, d209995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59961 q ha hb
    | true =>
      simp only [d23713, d209995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59940 q ha hb
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d211199 q = 1) : d209996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211199, d209996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211199, d209996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d23757 q = 1) (hb : d208035 q = 1) : d210001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23757, d210001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59962 q ha hb
    | true =>
      simp only [d23757, d210001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23758 q = 1) (hb : d208035 q = 1) : d210002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23758, d210002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23758, d210002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208035 q = 1) (hb : d211200 q = 1) : d210003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211200, d210003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211200, d210003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208035 q = 1) (hb : d211201 q = 1) : d210004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211201, d210004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211201, d210004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d211202 q = 1) : d210005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211202, d210005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211202, d210005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d211203 q = 1) : d210006 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211203, d210006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211203, d210006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59964 (p : Pattern) (ha : d23763 p = 1) (hb : d208035 p = 1) : d210007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208035 q = 1) : d209931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59938 q ha hb
    | true =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208035 q = 1) : d209932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208035 q = 1) : d209937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23649 q = 1) (hb : d208035 q = 1) : d209938 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23649, d209938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23649, d209938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23675 q = 1) (hb : d208035 q = 1) : d209964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23675, d209964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23675, d209964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23763 q = 1) (hb : d208035 q = 1) : d210007 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23763, d210007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23763, d210007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59965 (p : Pattern) (ha : d23764 p = 1) (hb : d208035 p = 1) : d210008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208035 q = 1) : d209941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23653 q = 1) (hb : d208035 q = 1) : d209942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23653, d209942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23653, d209942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23677 q = 1) (hb : d208035 q = 1) : d209966 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23677, d209966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23677, d209966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23764 q = 1) (hb : d208035 q = 1) : d210008 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23764, d210008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23764, d210008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59966 (p : Pattern) (ha : d23769 p = 1) (hb : d208035 p = 1) : d210013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208035 q = 1) : d209931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59938 q ha hb
    | true =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208035 q = 1) : d209932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23648 q = 1) (hb : d208035 q = 1) : d209937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23648, d209937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23683 q = 1) (hb : d208035 q = 1) : d209972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23683, d209972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23683, d209972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23684 q = 1) (hb : d208035 q = 1) : d209973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23684, d209973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23684, d209973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23769 q = 1) (hb : d208035 q = 1) : d210013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23769, d210013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23769, d210013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59967 (p : Pattern) (ha : d23770 p = 1) (hb : d208035 p = 1) : d210014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23646 q = 1) (hb : d208035 q = 1) : d209935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59939 q ha hb
    | true =>
      simp only [d23646, d209935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23647 q = 1) (hb : d208035 q = 1) : d209936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23647, d209936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23652 q = 1) (hb : d208035 q = 1) : d209941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23652, d209941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23686 q = 1) (hb : d208035 q = 1) : d209975 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23686, d209975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23686, d209975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23687 q = 1) (hb : d208035 q = 1) : d209976 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23687, d209976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23687, d209976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23770 q = 1) (hb : d208035 q = 1) : d210014 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23770, d210014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23770, d210014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59968 (p : Pattern) (ha : d23774 p = 1) (hb : d208035 p = 1) : d210018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23707 q = 1) (hb : d208035 q = 1) : d209989 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23707, d209989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59960 q ha hb
    | true =>
      simp only [d23707, d209989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23708 q = 1) (hb : d208035 q = 1) : d209990 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23708, d209990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23708, d209990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23642 q = 1) (hb : d208035 q = 1) : d209931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59938 q ha hb
    | true =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23643 q = 1) (hb : d208035 q = 1) : d209932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23709 q = 1) (hb : d208035 q = 1) : d209991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23709, d209991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23709, d209991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23710 q = 1) (hb : d208035 q = 1) : d209992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23710, d209992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23710, d209992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23711 q = 1) (hb : d208035 q = 1) : d209993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23711, d209993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23711, d209993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23774 q = 1) (hb : d208035 q = 1) : d210018 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23774, d210018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23774, d210018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59969 (p : Pattern) (ha : d23780 p = 1) (hb : d208035 p = 1) : d210021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23642 q = 1) (hb : d208035 q = 1) : d209931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59938 q ha hb
    | true =>
      simp only [d23642, d209931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23643 q = 1) (hb : d208035 q = 1) : d209932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23643, d209932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23753 q = 1) (hb : d208035 q = 1) : d209997 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23753, d209997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23753, d209997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23754 q = 1) (hb : d208035 q = 1) : d209998 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23754, d209998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23754, d209998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23755 q = 1) (hb : d208035 q = 1) : d209999 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23755, d209999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23755, d209999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23780 q = 1) (hb : d208035 q = 1) : d210021 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23780, d210021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23780, d210021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59970 (p : Pattern) (ha : d208035 p = 1) (hb : d211208 p = 1) : d210027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23679 q = 1) (hb : d208035 q = 1) : d209968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23679, d209968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59954 q ha hb
    | true =>
      simp only [d23679, d209968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59955 q ha hb
  have h2 (q : Pattern) (ha : d23680 q = 1) (hb : d208035 q = 1) : d209969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23680, d209969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23680, d209969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23681 q = 1) (hb : d208035 q = 1) : d209970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23681, d209970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23681, d209970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23682 q = 1) (hb : d208035 q = 1) : d209971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23682, d209971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23682, d209971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23689 q = 1) (hb : d208035 q = 1) : d209978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23689, d209978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59956 q ha hb
    | true =>
      simp only [d23689, d209978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59957 q ha hb
  have h6 (q : Pattern) (ha : d23690 q = 1) (hb : d208035 q = 1) : d209979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23690, d209979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23690, d209979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23691 q = 1) (hb : d208035 q = 1) : d209980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23691, d209980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23691, d209980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23713 q = 1) (hb : d208035 q = 1) : d209995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23713, d209995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59961 q ha hb
    | true =>
      simp only [d23713, d209995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59940 q ha hb
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d211199 q = 1) : d209996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211199, d209996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d211199, d209996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d23757 q = 1) (hb : d208035 q = 1) : d210001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23757, d210001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59962 q ha hb
    | true =>
      simp only [d23757, d210001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23758 q = 1) (hb : d208035 q = 1) : d210002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23758, d210002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23758, d210002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d208035 q = 1) (hb : d211200 q = 1) : d210003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211200, d210003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211200, d210003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d208035 q = 1) (hb : d211201 q = 1) : d210004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211201, d210004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211201, d210004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d211202 q = 1) : d210005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211202, d210005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211202, d210005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23765 q = 1) (hb : d208035 q = 1) : d210009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23765, d210009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59964 q ha hb
    | true =>
      simp only [d23765, d210009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59965 q ha hb
  have h16 (q : Pattern) (ha : d23766 q = 1) (hb : d208035 q = 1) : d210010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23766, d210010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23766, d210010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23767 q = 1) (hb : d208035 q = 1) : d210011 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23767, d210011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23767, d210011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23768 q = 1) (hb : d208035 q = 1) : d210012 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23768, d210012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23768, d210012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23771 q = 1) (hb : d208035 q = 1) : d210015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23771, d210015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59966 q ha hb
    | true =>
      simp only [d23771, d210015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59967 q ha hb
  have h20 (q : Pattern) (ha : d23772 q = 1) (hb : d208035 q = 1) : d210016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23772, d210016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23772, d210016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23773 q = 1) (hb : d208035 q = 1) : d210017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23773, d210017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d23773, d210017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d23775 q = 1) (hb : d208035 q = 1) : d210019 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23775, d210019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59968 q ha hb
    | true =>
      simp only [d23775, d210019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59943 q ha hb
  have h23 (q : Pattern) (ha : d208035 q = 1) (hb : d211204 q = 1) : d210020 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211204, d210020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d211204, d210020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d23781 q = 1) (hb : d208035 q = 1) : d210022 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23781, d210022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59969 q ha hb
    | true =>
      simp only [d23781, d210022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d23782 q = 1) (hb : d208035 q = 1) : d210023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23782, d210023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23782, d210023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d208035 q = 1) (hb : d211205 q = 1) : d210024 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211205, d210024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d211205, d210024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d208035 q = 1) (hb : d211206 q = 1) : d210025 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211206, d210025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d211206, d210025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d208035 q = 1) (hb : d211207 q = 1) : d210026 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211207, d210026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d211207, d210026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d208035 q = 1) (hb : d211208 q = 1) : d210027 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211208, d210027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211208, d210027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro59971 (p : Pattern) (ha : d208035 p = 1) (hb : d211215 p = 1) : d210047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23775 q = 1) (hb : d208035 q = 1) : d210019 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23775, d210019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59968 q ha hb
    | true =>
      simp only [d23775, d210019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59943 q ha hb
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d211204 q = 1) : d210020 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211204, d210020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211204, d210020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23781 q = 1) (hb : d208035 q = 1) : d210022 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23781, d210022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59969 q ha hb
    | true =>
      simp only [d23781, d210022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23782 q = 1) (hb : d208035 q = 1) : d210023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23782, d210023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23782, d210023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211205 q = 1) : d210024 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211205, d210024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211205, d210024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211213 q = 1) : d210045 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211213, d210045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211213, d210045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211214 q = 1) : d210046 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211214, d210046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211214, d210046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211215 q = 1) : d210047 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211215, d210047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211215, d210047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59972 (p : Pattern) (ha : d23819 p = 1) (hb : d208035 p = 1) : d210056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23814 q = 1) (hb : d208035 q = 1) : d22033 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23814, d22033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23814, d22033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59958 q ha hb
  have h2 (q : Pattern) (ha : d23695 q = 1) (hb : d208035 q = 1) : d21841 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59958 q ha hb
    | true =>
      simp only [d23695, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23815 q = 1) (hb : d208035 q = 1) : d22034 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23815, d22034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23815, d22034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23696 q = 1) (hb : d208035 q = 1) : d21842 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23696, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23816 q = 1) (hb : d208035 q = 1) : d22035 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23816, d22035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23816, d22035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23817 q = 1) (hb : d208035 q = 1) : d22036 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23817, d22036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23817, d22036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23534 q = 1) (hb : d208035 q = 1) : d200839 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d200839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d200839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59912 q ha hb
  have h8 (q : Pattern) (ha : d23422 q = 1) (hb : d208035 q = 1) : d200752 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59912 q ha hb
    | true =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23535 q = 1) (hb : d208035 q = 1) : d200840 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d200840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23535, d200840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23423 q = 1) (hb : d208035 q = 1) : d200753 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23536 q = 1) (hb : d208035 q = 1) : d200841 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d200841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23536, d200841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23537 q = 1) (hb : d208035 q = 1) : d200842 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d200842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23537, d200842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23818 q = 1) (hb : d208035 q = 1) : d210055 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23818, d210055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23818, d210055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23310 q = 1) (hb : d208035 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
  have h15 (q : Pattern) (ha : d23231 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
    | true =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23311 q = 1) (hb : d208035 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23311, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23232 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23312 q = 1) (hb : d208035 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23312, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23313 q = 1) (hb : d208035 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23313, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23538 q = 1) (hb : d208035 q = 1) : d200843 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d200843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23538, d200843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23819 q = 1) (hb : d208035 q = 1) : d210056 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23819, d210056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23819, d210056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro59973 (p : Pattern) (ha : d23821 p = 1) (hb : d208035 p = 1) : d209856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23534 q = 1) (hb : d208035 q = 1) : d200839 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d200839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d200839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59912 q ha hb
  have h2 (q : Pattern) (ha : d23422 q = 1) (hb : d208035 q = 1) : d200752 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59912 q ha hb
    | true =>
      simp only [d23422, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23535 q = 1) (hb : d208035 q = 1) : d200840 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d200840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23535, d200840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23423 q = 1) (hb : d208035 q = 1) : d200753 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23423, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23536 q = 1) (hb : d208035 q = 1) : d200841 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d200841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23536, d200841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23537 q = 1) (hb : d208035 q = 1) : d200842 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d200842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23537, d200842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23310 q = 1) (hb : d208035 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
  have h8 (q : Pattern) (ha : d23231 q = 1) (hb : d208035 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59875 q ha hb
    | true =>
      simp only [d23231, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23311 q = 1) (hb : d208035 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23311, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23232 q = 1) (hb : d208035 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23232, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23312 q = 1) (hb : d208035 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23312, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23313 q = 1) (hb : d208035 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23313, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23538 q = 1) (hb : d208035 q = 1) : d200843 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d200843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23538, d200843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h20 (q : Pattern) (ha : d23820 q = 1) (hb : d208035 q = 1) : d200615 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23820, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23820, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d23821 q = 1) (hb : d208035 q = 1) : d209856 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23821, d209856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23821, d209856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro59974 (p : Pattern) (ha : d23835 p = 1) (hb : d208035 p = 1) : d210072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23822 q = 1) (hb : d208035 q = 1) : d210057 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23822, d210057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59972 q ha hb
    | true =>
      simp only [d23822, d210057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59973 q ha hb
  have h2 (q : Pattern) (ha : d23823 q = 1) (hb : d208035 q = 1) : d210058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23823, d210058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23823, d210058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23824 q = 1) (hb : d208035 q = 1) : d210059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23824, d210059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23824, d210059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23826 q = 1) (hb : d208035 q = 1) : d210062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23826, d210062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59973 q ha hb
    | true =>
      simp only [d23826, d210062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59950 q ha hb
  have h5 (q : Pattern) (ha : d23827 q = 1) (hb : d208035 q = 1) : d210063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23827, d210063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23827, d210063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23828 q = 1) (hb : d208035 q = 1) : d210064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23828, d210064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23828, d210064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23829 q = 1) (hb : d208035 q = 1) : d210065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23829, d210065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23829, d210065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23830 q = 1) (hb : d208035 q = 1) : d210067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23830, d210067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59950 q ha hb
    | true =>
      simp only [d23830, d210067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59949 q ha hb
  have h9 (q : Pattern) (ha : d23831 q = 1) (hb : d208035 q = 1) : d210068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23831, d210068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23831, d210068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23832 q = 1) (hb : d208035 q = 1) : d210069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23832, d210069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23832, d210069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23833 q = 1) (hb : d208035 q = 1) : d210070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23833, d210070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23833, d210070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23834 q = 1) (hb : d208035 q = 1) : d210071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23834, d210071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23834, d210071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23835 q = 1) (hb : d208035 q = 1) : d210072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23835, d210072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23835, d210072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro59975 (p : Pattern) (ha : d23840 p = 1) (hb : d208035 p = 1) : d210077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23826 q = 1) (hb : d208035 q = 1) : d210062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23826, d210062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59973 q ha hb
    | true =>
      simp only [d23826, d210062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59950 q ha hb
  have h2 (q : Pattern) (ha : d23827 q = 1) (hb : d208035 q = 1) : d210063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23827, d210063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23827, d210063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23828 q = 1) (hb : d208035 q = 1) : d210064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23828, d210064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23828, d210064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23830 q = 1) (hb : d208035 q = 1) : d210067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23830, d210067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59950 q ha hb
    | true =>
      simp only [d23830, d210067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59949 q ha hb
  have h5 (q : Pattern) (ha : d23831 q = 1) (hb : d208035 q = 1) : d210068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23831, d210068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23831, d210068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23832 q = 1) (hb : d208035 q = 1) : d210069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23832, d210069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23832, d210069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23833 q = 1) (hb : d208035 q = 1) : d210070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23833, d210070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23833, d210070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23838 q = 1) (hb : d208035 q = 1) : d210075 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23838, d210075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23838, d210075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23839 q = 1) (hb : d208035 q = 1) : d210076 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23839, d210076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23839, d210076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23840 q = 1) (hb : d208035 q = 1) : d210077 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23840, d210077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23840, d210077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro59976 (p : Pattern) (ha : d23846 p = 1) (hb : d208035 p = 1) : d210083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23836 q = 1) (hb : d208035 q = 1) : d210073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23836, d210073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59974 q ha hb
    | true =>
      simp only [d23836, d210073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23837 q = 1) (hb : d208035 q = 1) : d210074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23837, d210074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23837, d210074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23841 q = 1) (hb : d208035 q = 1) : d210078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23841, d210078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59975 q ha hb
    | true =>
      simp only [d23841, d210078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23842 q = 1) (hb : d208035 q = 1) : d210079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23842, d210079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23842, d210079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23843 q = 1) (hb : d208035 q = 1) : d210080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23843, d210080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23843, d210080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23844 q = 1) (hb : d208035 q = 1) : d210081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23844, d210081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23844, d210081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23845 q = 1) (hb : d208035 q = 1) : d210082 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23845, d210082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23845, d210082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23846 q = 1) (hb : d208035 q = 1) : d210083 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23846, d210083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23846, d210083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59977 (p : Pattern) (ha : d23854 p = 1) (hb : d208035 p = 1) : d210091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23841 q = 1) (hb : d208035 q = 1) : d210078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23841, d210078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59975 q ha hb
    | true =>
      simp only [d23841, d210078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23842 q = 1) (hb : d208035 q = 1) : d210079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23842, d210079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23842, d210079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23849 q = 1) (hb : d208035 q = 1) : d210086 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23849, d210086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59951 q ha hb
    | true =>
      simp only [d23849, d210086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23850 q = 1) (hb : d208035 q = 1) : d210087 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23850, d210087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23850, d210087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23851 q = 1) (hb : d208035 q = 1) : d210088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23851, d210088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23851, d210088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23852 q = 1) (hb : d208035 q = 1) : d210089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23852, d210089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23852, d210089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23853 q = 1) (hb : d208035 q = 1) : d210090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23853, d210090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23853, d210090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23854 q = 1) (hb : d208035 q = 1) : d210091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23854, d210091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23854, d210091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59978 (p : Pattern) (ha : d23895 p = 1) (hb : d208035 p = 1) : d210097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23841 q = 1) (hb : d208035 q = 1) : d210078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23841, d210078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59975 q ha hb
    | true =>
      simp only [d23841, d210078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23842 q = 1) (hb : d208035 q = 1) : d210079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23842, d210079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23842, d210079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23892 q = 1) (hb : d208035 q = 1) : d210094 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23892, d210094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23892, d210094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23893 q = 1) (hb : d208035 q = 1) : d210095 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23893, d210095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23893, d210095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23894 q = 1) (hb : d208035 q = 1) : d210096 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23894, d210096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23894, d210096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23895 q = 1) (hb : d208035 q = 1) : d210097 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23895, d210097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23895, d210097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59979 (p : Pattern) (ha : d208035 p = 1) (hb : d211225 p = 1) : d210103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23855 q = 1) (hb : d208035 q = 1) : d210092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23855, d210092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59976 q ha hb
    | true =>
      simp only [d23855, d210092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59977 q ha hb
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d211221 q = 1) : d210093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211221, d210093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211221, d210093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23896 q = 1) (hb : d208035 q = 1) : d210098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23896, d210098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59978 q ha hb
    | true =>
      simp only [d23896, d210098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23897 q = 1) (hb : d208035 q = 1) : d210099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23897, d210099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23897, d210099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211222 q = 1) : d210100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211222, d210100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211222, d210100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211223 q = 1) : d210101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211223, d210101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211223, d210101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208035 q = 1) (hb : d211224 q = 1) : d210102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211224, d210102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211224, d210102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211225 q = 1) : d210103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211225, d210103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211225, d210103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59980 (p : Pattern) (ha : d208035 p = 1) (hb : d211231 p = 1) : d210120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23662 q = 1) (hb : d208035 q = 1) : d209951 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23662, d209951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23662, d209951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59942 q ha hb
  have h2 (q : Pattern) (ha : d23663 q = 1) (hb : d208035 q = 1) : d209952 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23663, d209952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23663, d209952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23672 q = 1) (hb : d208035 q = 1) : d209961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23672, d209961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59942 q ha hb
    | true =>
      simp only [d23672, d209961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59945 q ha hb
  have h4 (q : Pattern) (ha : d23673 q = 1) (hb : d208035 q = 1) : d209962 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23673, d209962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23673, d209962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23674 q = 1) (hb : d208035 q = 1) : d209963 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d23674, d209963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23674, d209963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211209 q = 1) : d210028 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211209, d210028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59963 q ha hb
    | true =>
      simp only [d211209, d210028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59970 q ha hb
  have h7 (q : Pattern) (ha : d23800 q = 1) (hb : d208035 q = 1) : d210041 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23800, d210041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59946 q ha hb
    | true =>
      simp only [d23800, d210041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59947 q ha hb
  have h8 (q : Pattern) (ha : d208035 q = 1) (hb : d211210 q = 1) : d210042 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211210, d210042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211210, d210042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d208035 q = 1) (hb : d211211 q = 1) : d210043 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211211, d210043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211211, d210043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d208035 q = 1) (hb : d211212 q = 1) : d210044 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211212, d210044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d211212, d210044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208035 q = 1) (hb : d211216 q = 1) : d210048 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211216, d210048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211216, d210048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59971 q ha hb
  have h12 (q : Pattern) (ha : d23809 q = 1) (hb : d208035 q = 1) : d210050 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23809, d210050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23809, d210050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59948 q ha hb
  have h13 (q : Pattern) (ha : d208035 q = 1) (hb : d211217 q = 1) : d210051 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211217, d210051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d211217, d210051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d208035 q = 1) (hb : d211218 q = 1) : d210052 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211218, d210052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211218, d210052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208035 q = 1) (hb : d211219 q = 1) : d210053 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211219, d210053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211219, d210053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d208035 q = 1) (hb : d211220 q = 1) : d210054 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211220, d210054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211220, d210054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208035 q = 1) (hb : d211226 q = 1) : d210104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211226, d210104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211226, d210104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59979 q ha hb
  have h18 (q : Pattern) (ha : d23913 q = 1) (hb : d208035 q = 1) : d210115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23913, d210115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23913, d210115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59953 q ha hb
  have h19 (q : Pattern) (ha : d208035 q = 1) (hb : d211227 q = 1) : d210116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211227, d210116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211227, d210116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d208035 q = 1) (hb : d211228 q = 1) : d210117 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211228, d210117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d211228, d210117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d208035 q = 1) (hb : d211229 q = 1) : d210118 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211229, d210118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d211229, d210118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d208035 q = 1) (hb : d211230 q = 1) : d210119 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211230, d210119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211230, d210119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d208035 q = 1) (hb : d211231 q = 1) : d210120 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211231, d210120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211231, d210120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro59981 (p : Pattern) (ha : d208035 p = 1) (hb : d211237 p = 1) : d210126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208035 q = 1) (hb : d211232 q = 1) : d210121 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211232, d210121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211232, d210121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59980 q ha hb
  have h2 (q : Pattern) (ha : d208035 q = 1) (hb : d211233 q = 1) : d210122 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211233, d210122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211233, d210122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208035 q = 1) (hb : d211234 q = 1) : d210123 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211234, d210123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211234, d210123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208035 q = 1) (hb : d211235 q = 1) : d210124 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211235, d210124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211235, d210124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208035 q = 1) (hb : d211236 q = 1) : d210125 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211236, d210125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211236, d210125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208035 q = 1) (hb : d211237 q = 1) : d210126 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211237, d210126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211237, d210126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59982 (p : Pattern) (ha : d23931 p = 1) (hb : d208035 p = 1) : d21840 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d823 q = 1) : d823 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1089 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1090 q = 1) (hb : d152852 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1090, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23927 q = 1) (hb : d208034 q = 1) : d9760 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23927, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23927, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23928 q = 1) (hb : d208034 q = 1) : d9761 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23928, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23928, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d23930 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23931 q = 1) (hb : d208035 q = 1) : d21840 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23931, d208035, d21840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23931, d208035, d21840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59983 (p : Pattern) (ha : d23938 p = 1) (hb : d208035 p = 1) : d200927 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1089 q = 1) : d1089 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1096 q = 1) (hb : d152852 q = 1) : d26079 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1096, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23929 q = 1) (hb : d208034 q = 1) : d26098 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23929, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23929, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23930 q = 1) (hb : d208034 q = 1) : d26099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23930, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23930, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d23937 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23938 q = 1) (hb : d208035 q = 1) : d200927 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23938, d208035, d200927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23938, d208035, d200927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59984 (p : Pattern) (ha : d23944 p = 1) (hb : d208035 p = 1) : d210129 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1095 q = 1) : d1095 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1106 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1106, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23936 q = 1) (hb : d208034 q = 1) : d26090 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23936, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23936, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23937 q = 1) (hb : d208034 q = 1) : d26091 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23937, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23937, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d5538 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23944 q = 1) (hb : d208035 q = 1) : d210129 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23944, d208035, d210129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23944, d208035, d210129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro59985 (p : Pattern) (ha : d23950 p = 1) (hb : d208035 p = 1) : d210135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23932 q = 1) (hb : d208035 q = 1) : d21841 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23932, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59982 q ha hb
    | true =>
      simp only [d23932, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23933 q = 1) (hb : d208035 q = 1) : d21842 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23933, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23933, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23934 q = 1) (hb : d208035 q = 1) : d21843 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23934, d21843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23934, d21843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23935 q = 1) (hb : d208035 q = 1) : d21844 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23935, d21844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23935, d21844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23939 q = 1) (hb : d208035 q = 1) : d200928 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59983 q ha hb
    | true =>
      simp only [d23939, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23940 q = 1) (hb : d208035 q = 1) : d200929 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23940, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23941 q = 1) (hb : d208035 q = 1) : d200930 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23942 q = 1) (hb : d208035 q = 1) : d200931 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23942, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23943 q = 1) (hb : d208035 q = 1) : d201009 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23943, d201009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23943, d201009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23945 q = 1) (hb : d208035 q = 1) : d210130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d210130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59984 q ha hb
    | true =>
      simp only [d23945, d210130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23946 q = 1) (hb : d208035 q = 1) : d210131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d210131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23946, d210131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23947 q = 1) (hb : d208035 q = 1) : d210132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d210132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d210132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23948 q = 1) (hb : d208035 q = 1) : d210133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d210133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23948, d210133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23949 q = 1) (hb : d208035 q = 1) : d210134 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23949, d210134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23949, d210134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23950 q = 1) (hb : d208035 q = 1) : d210135 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23950, d210135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23950, d210135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59986 (p : Pattern) (ha : d23952 p = 1) (hb : d208035 p = 1) : d210137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23939 q = 1) (hb : d208035 q = 1) : d200928 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59983 q ha hb
    | true =>
      simp only [d23939, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23940 q = 1) (hb : d208035 q = 1) : d200929 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23940, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23941 q = 1) (hb : d208035 q = 1) : d200930 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23942 q = 1) (hb : d208035 q = 1) : d200931 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23942, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23945 q = 1) (hb : d208035 q = 1) : d210130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d210130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59984 q ha hb
    | true =>
      simp only [d23945, d210130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23946 q = 1) (hb : d208035 q = 1) : d210131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d210131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23946, d210131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23947 q = 1) (hb : d208035 q = 1) : d210132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d210132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d210132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23948 q = 1) (hb : d208035 q = 1) : d210133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d210133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23948, d210133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23949 q = 1) (hb : d208035 q = 1) : d210134 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23949, d210134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23949, d210134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23951 q = 1) (hb : d208035 q = 1) : d210136 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23951, d210136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23951, d210136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23952 q = 1) (hb : d208035 q = 1) : d210137 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23952, d210137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23952, d210137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59987 (p : Pattern) (ha : d23956 p = 1) (hb : d208035 p = 1) : d210141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23945 q = 1) (hb : d208035 q = 1) : d210130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d210130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59984 q ha hb
    | true =>
      simp only [d23945, d210130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23946 q = 1) (hb : d208035 q = 1) : d210131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d210131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23946, d210131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23947 q = 1) (hb : d208035 q = 1) : d210132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d210132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d210132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23948 q = 1) (hb : d208035 q = 1) : d210133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d210133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23948, d210133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23951 q = 1) (hb : d208035 q = 1) : d210136 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23951, d210136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23951, d210136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1140 q = 1) (hb : d208035 q = 1) : d1140 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23956 q = 1) (hb : d208035 q = 1) : d210141 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23956, d210141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23956, d210141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro59988 (p : Pattern) (ha : d23963 p = 1) (hb : d208035 p = 1) : d210148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23953 q = 1) (hb : d208035 q = 1) : d210138 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23953, d210138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59985 q ha hb
    | true =>
      simp only [d23953, d210138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59986 q ha hb
  have h2 (q : Pattern) (ha : d23954 q = 1) (hb : d208035 q = 1) : d210139 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23954, d210139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23954, d210139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23955 q = 1) (hb : d208035 q = 1) : d210140 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23955, d210140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23955, d210140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23957 q = 1) (hb : d208035 q = 1) : d210142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d210142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59986 q ha hb
    | true =>
      simp only [d23957, d210142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59987 q ha hb
  have h5 (q : Pattern) (ha : d23958 q = 1) (hb : d208035 q = 1) : d210143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d210143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d210143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23959 q = 1) (hb : d208035 q = 1) : d210144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d210144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d210144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23960 q = 1) (hb : d208035 q = 1) : d210145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23960, d210145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23960, d210145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23961 q = 1) (hb : d208035 q = 1) : d210146 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23961, d210146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23961, d210146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23962 q = 1) (hb : d208035 q = 1) : d210147 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23962, d210147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23962, d210147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23963 q = 1) (hb : d208035 q = 1) : d210148 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23963, d210148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23963, d210148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro59989 (p : Pattern) (ha : d23967 p = 1) (hb : d208035 p = 1) : d210152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23957 q = 1) (hb : d208035 q = 1) : d210142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d210142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59986 q ha hb
    | true =>
      simp only [d23957, d210142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59987 q ha hb
  have h2 (q : Pattern) (ha : d23958 q = 1) (hb : d208035 q = 1) : d210143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d210143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d210143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23959 q = 1) (hb : d208035 q = 1) : d210144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d210144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d210144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23961 q = 1) (hb : d208035 q = 1) : d210146 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23961, d210146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23961, d210146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23966 q = 1) (hb : d208035 q = 1) : d210151 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23966, d210151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23966, d210151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23967 q = 1) (hb : d208035 q = 1) : d210152 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23967, d210152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23967, d210152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59990 (p : Pattern) (ha : d23973 p = 1) (hb : d208035 p = 1) : d210158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d208035 q = 1) : d210149 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d210149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59988 q ha hb
    | true =>
      simp only [d23964, d210149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d208035 q = 1) : d210150 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d210150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d210150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d208035 q = 1) : d210153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d210153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59989 q ha hb
    | true =>
      simp only [d23968, d210153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d208035 q = 1) : d210154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d210154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d210154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d208035 q = 1) : d210155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d210155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d210155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d208035 q = 1) : d210156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d210156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d210156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23972 q = 1) (hb : d208035 q = 1) : d210157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23972, d210157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23972, d210157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23973 q = 1) (hb : d208035 q = 1) : d210158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23973, d210158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23973, d210158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59991 (p : Pattern) (ha : d23977 p = 1) (hb : d208035 p = 1) : d210162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d208035 q = 1) : d210153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d210153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59989 q ha hb
    | true =>
      simp only [d23968, d210153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d208035 q = 1) : d210154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d210154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d210154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d208035 q = 1) : d210159 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d210159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d210159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23975 q = 1) (hb : d208035 q = 1) : d210160 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23975, d210160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23975, d210160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23976 q = 1) (hb : d208035 q = 1) : d210161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23976, d210161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23976, d210161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23977 q = 1) (hb : d208035 q = 1) : d210162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23977, d210162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23977, d210162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59992 (p : Pattern) (ha : d23983 p = 1) (hb : d208035 p = 1) : d210168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23978 q = 1) (hb : d208035 q = 1) : d210163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59990 q ha hb
    | true =>
      simp only [d23978, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59991 q ha hb
  have h2 (q : Pattern) (ha : d23979 q = 1) (hb : d208035 q = 1) : d210164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23979, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23980 q = 1) (hb : d208035 q = 1) : d210165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23980, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23981 q = 1) (hb : d208035 q = 1) : d210166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23981, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23982 q = 1) (hb : d208035 q = 1) : d210167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23983 q = 1) (hb : d208035 q = 1) : d210168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23983, d210168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23983, d210168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59993 (p : Pattern) (ha : d23986 p = 1) (hb : d208035 p = 1) : d210171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d208035 q = 1) : d210149 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d210149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59988 q ha hb
    | true =>
      simp only [d23964, d210149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d208035 q = 1) : d210150 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d210150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d210150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d208035 q = 1) : d210153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d210153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59989 q ha hb
    | true =>
      simp only [d23968, d210153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d208035 q = 1) : d210154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d210154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d210154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d208035 q = 1) : d210155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d210155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d210155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d208035 q = 1) : d210156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d210156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d210156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23972 q = 1) (hb : d208035 q = 1) : d210157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23972, d210157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23972, d210157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23986 q = 1) (hb : d208035 q = 1) : d210171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23986, d210171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23986, d210171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59994 (p : Pattern) (ha : d23987 p = 1) (hb : d208035 p = 1) : d210172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d208035 q = 1) : d210153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d210153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59989 q ha hb
    | true =>
      simp only [d23968, d210153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d208035 q = 1) : d210154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d210154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d210154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d208035 q = 1) : d210159 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d210159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d210159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23975 q = 1) (hb : d208035 q = 1) : d210160 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23975, d210160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23975, d210160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23976 q = 1) (hb : d208035 q = 1) : d210161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23976, d210161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23976, d210161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23987 q = 1) (hb : d208035 q = 1) : d210172 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23987, d210172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23987, d210172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro59995 (p : Pattern) (ha : d23993 p = 1) (hb : d208035 p = 1) : d210178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23978 q = 1) (hb : d208035 q = 1) : d210163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59990 q ha hb
    | true =>
      simp only [d23978, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59991 q ha hb
  have h2 (q : Pattern) (ha : d23979 q = 1) (hb : d208035 q = 1) : d210164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23979, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23980 q = 1) (hb : d208035 q = 1) : d210165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23980, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23981 q = 1) (hb : d208035 q = 1) : d210166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23981, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23982 q = 1) (hb : d208035 q = 1) : d210167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23988 q = 1) (hb : d208035 q = 1) : d210173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23988, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59993 q ha hb
    | true =>
      simp only [d23988, d210173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59994 q ha hb
  have h7 (q : Pattern) (ha : d23989 q = 1) (hb : d208035 q = 1) : d210174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23989, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23989, d210174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23990 q = 1) (hb : d208035 q = 1) : d210175 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23990, d210175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23991 q = 1) (hb : d208035 q = 1) : d210176 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23991, d210176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23992 q = 1) (hb : d208035 q = 1) : d210177 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23992, d210177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23993 q = 1) (hb : d208035 q = 1) : d210178 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23993, d210178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23993, d210178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59996 (p : Pattern) (ha : d24140 p = 1) (hb : d208035 p = 1) : d210261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23978 q = 1) (hb : d208035 q = 1) : d210163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59990 q ha hb
    | true =>
      simp only [d23978, d210163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59991 q ha hb
  have h2 (q : Pattern) (ha : d23979 q = 1) (hb : d208035 q = 1) : d210164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23979, d210164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23980 q = 1) (hb : d208035 q = 1) : d210165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23980, d210165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23981 q = 1) (hb : d208035 q = 1) : d210166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23981, d210166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23982 q = 1) (hb : d208035 q = 1) : d210167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d210167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24135 q = 1) (hb : d208035 q = 1) : d210256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24135, d210256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59991 q ha hb
    | true =>
      simp only [d24135, d210256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24136 q = 1) (hb : d208035 q = 1) : d210257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24136, d210257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24136, d210257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24137 q = 1) (hb : d208035 q = 1) : d210258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24137, d210258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24137, d210258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24138 q = 1) (hb : d208035 q = 1) : d210259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24138, d210259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24138, d210259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24139 q = 1) (hb : d208035 q = 1) : d210260 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24139, d210260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24139, d210260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24140 q = 1) (hb : d208035 q = 1) : d210261 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24140, d210261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24140, d210261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59997 (p : Pattern) (ha : d24146 p = 1) (hb : d208035 p = 1) : d210267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24135 q = 1) (hb : d208035 q = 1) : d210256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24135, d210256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59991 q ha hb
    | true =>
      simp only [d24135, d210256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24136 q = 1) (hb : d208035 q = 1) : d210257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24136, d210257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24136, d210257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24137 q = 1) (hb : d208035 q = 1) : d210258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24137, d210258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24137, d210258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24138 q = 1) (hb : d208035 q = 1) : d210259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24138, d210259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24138, d210259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24139 q = 1) (hb : d208035 q = 1) : d210260 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24139, d210260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24139, d210260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24141 q = 1) (hb : d208035 q = 1) : d210262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24141, d210262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59994 q ha hb
    | true =>
      simp only [d24141, d210262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24142 q = 1) (hb : d208035 q = 1) : d210263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24142, d210263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24142, d210263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24143 q = 1) (hb : d208035 q = 1) : d210264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24143, d210264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24143, d210264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24144 q = 1) (hb : d208035 q = 1) : d210265 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24144, d210265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24144, d210265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24145 q = 1) (hb : d208035 q = 1) : d210266 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24145, d210266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24145, d210266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24146 q = 1) (hb : d208035 q = 1) : d210267 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24146, d210267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24146, d210267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59998 (p : Pattern) (ha : d24155 p = 1) (hb : d208035 p = 1) : d210276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24141 q = 1) (hb : d208035 q = 1) : d210262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24141, d210262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59994 q ha hb
    | true =>
      simp only [d24141, d210262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24142 q = 1) (hb : d208035 q = 1) : d210263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24142, d210263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24142, d210263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24143 q = 1) (hb : d208035 q = 1) : d210264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24143, d210264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24143, d210264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24144 q = 1) (hb : d208035 q = 1) : d210265 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24144, d210265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24144, d210265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24145 q = 1) (hb : d208035 q = 1) : d210266 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24145, d210266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24145, d210266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24155 q = 1) (hb : d208035 q = 1) : d210276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24155, d210276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24155, d210276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59999 (p : Pattern) (ha : d24186 p = 1) (hb : d208035 p = 1) : d210294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24170 q = 1) (hb : d208035 q = 1) : d201101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24170, d201101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24170, d201101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59983 q ha hb
  have h2 (q : Pattern) (ha : d23939 q = 1) (hb : d208035 q = 1) : d200928 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59983 q ha hb
    | true =>
      simp only [d23939, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24171 q = 1) (hb : d208035 q = 1) : d201102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24171, d201102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24171, d201102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23940 q = 1) (hb : d208035 q = 1) : d200929 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23940, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24172 q = 1) (hb : d208035 q = 1) : d201103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24172, d201103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24172, d201103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24173 q = 1) (hb : d208035 q = 1) : d201104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24173, d201104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24173, d201104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24176 q = 1) (hb : d208035 q = 1) : d210284 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24176, d210284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24176, d210284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59984 q ha hb
  have h8 (q : Pattern) (ha : d23945 q = 1) (hb : d208035 q = 1) : d210130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d210130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59984 q ha hb
    | true =>
      simp only [d23945, d210130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24177 q = 1) (hb : d208035 q = 1) : d210285 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24177, d210285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24177, d210285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23946 q = 1) (hb : d208035 q = 1) : d210131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d210131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23946, d210131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24178 q = 1) (hb : d208035 q = 1) : d210286 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24178, d210286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24178, d210286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24179 q = 1) (hb : d208035 q = 1) : d210287 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24179, d210287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24179, d210287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24180 q = 1) (hb : d208035 q = 1) : d210288 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24180, d210288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24180, d210288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24185 q = 1) (hb : d208035 q = 1) : d210293 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24185, d210293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24185, d210293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24186 q = 1) (hb : d208035 q = 1) : d210294 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24186, d210294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24186, d210294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
