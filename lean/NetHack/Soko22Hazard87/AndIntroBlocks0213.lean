import NetHack.Soko22Hazard87.AndIntroBlocks0212
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro53250 (p : Pattern) (ha : d171189 p = 1) (hb : d211415 p = 1) : d212460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171184 q = 1) (hb : d211415 q = 1) : d212455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171184, d212455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53249 q ha hb
    | true =>
      simp only [d171184, d212455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52986 q ha hb
  have h2 (q : Pattern) (ha : d171185 q = 1) (hb : d211415 q = 1) : d212456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171185, d212456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171185, d212456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171186 q = 1) (hb : d211415 q = 1) : d212457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171186, d212457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171186, d212457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171187 q = 1) (hb : d211415 q = 1) : d212458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171187, d212458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171187, d212458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171188 q = 1) (hb : d211415 q = 1) : d212459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171188, d212459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171188, d212459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171189 q = 1) (hb : d211415 q = 1) : d212460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171189, d212460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171189, d212460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53251 (p : Pattern) (ha : d171195 p = 1) (hb : d211415 p = 1) : d212466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16839 q = 1) (hb : d211415 q = 1) : d27610 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, d27610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52974 q ha hb
    | true =>
      simp only [d16839, d27610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52977 q ha hb
  have h2 (q : Pattern) (ha : d16840 q = 1) (hb : d211415 q = 1) : d27611 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, d27611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16840, d27611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171168 q = 1) (hb : d211415 q = 1) : d212439 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171168, d212439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171168, d212439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171169 q = 1) (hb : d211415 q = 1) : d212440 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171169, d212440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171169, d212440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171171 q = 1) (hb : d211415 q = 1) : d212442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171171, d212442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171171, d212442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53247 q ha hb
  have h6 (q : Pattern) (ha : d171172 q = 1) (hb : d211415 q = 1) : d212443 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171172, d212443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171172, d212443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171173 q = 1) (hb : d211415 q = 1) : d212444 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171173, d212444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171173, d212444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171174 q = 1) (hb : d211415 q = 1) : d212445 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171174, d212445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171174, d212445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171175 q = 1) (hb : d211415 q = 1) : d212446 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171175, d212446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171175, d212446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171190 q = 1) (hb : d211415 q = 1) : d212461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171190, d212461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171190, d212461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53250 q ha hb
  have h11 (q : Pattern) (ha : d171191 q = 1) (hb : d211415 q = 1) : d212462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171191, d212462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171191, d212462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171192 q = 1) (hb : d211415 q = 1) : d212463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171192, d212463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171192, d212463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171193 q = 1) (hb : d211415 q = 1) : d212464 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171193, d212464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171193, d212464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171194 q = 1) (hb : d211415 q = 1) : d212465 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171194, d212465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171194, d212465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171195 q = 1) (hb : d211415 q = 1) : d212466 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171195, d212466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171195, d212466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53252 (p : Pattern) (ha : d171201 p = 1) (hb : d211415 p = 1) : d212472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171196 q = 1) (hb : d211415 q = 1) : d212467 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171196, d212467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171196, d212467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53251 q ha hb
  have h2 (q : Pattern) (ha : d171197 q = 1) (hb : d211415 q = 1) : d212468 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171197, d212468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171197, d212468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171198 q = 1) (hb : d211415 q = 1) : d212469 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171198, d212469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171198, d212469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171199 q = 1) (hb : d211415 q = 1) : d212470 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171199, d212470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171199, d212470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171200 q = 1) (hb : d211415 q = 1) : d212471 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171200, d212471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171200, d212471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171201 q = 1) (hb : d211415 q = 1) : d212472 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171201, d212472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171201, d212472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53253 (p : Pattern) (ha : d171208 p = 1) (hb : d211415 p = 1) : d212479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17199 q = 1) (hb : d211415 q = 1) : d28218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d28218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53044 q ha hb
    | true =>
      simp only [d17199, d28218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53045 q ha hb
  have h2 (q : Pattern) (ha : d17200 q = 1) (hb : d211415 q = 1) : d28219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d28219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, d28219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17201 q = 1) (hb : d211415 q = 1) : d28220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d28220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17201, d28220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17202 q = 1) (hb : d211415 q = 1) : d28221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d28221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d28221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17203 q = 1) (hb : d211415 q = 1) : d28222 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d28222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d28222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171208 q = 1) (hb : d211415 q = 1) : d212479 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171208, d212479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171208, d212479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53254 (p : Pattern) (ha : d171215 p = 1) (hb : d211415 p = 1) : d212486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d211415 q = 1) : d28523 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d28523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53082 q ha hb
    | true =>
      simp only [d17397, d28523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53053 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d211415 q = 1) : d28524 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d28524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d28524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d211415 q = 1) : d28525 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d28525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d28525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d211415 q = 1) : d28537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d28537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53053 q ha hb
    | true =>
      simp only [d17400, d28537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53080 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d211415 q = 1) : d28538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d28538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d28538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d211415 q = 1) : d28539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d28539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d28539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d211415 q = 1) : d28540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d28540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d28540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17417 q = 1) (hb : d211415 q = 1) : d28560 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d28560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53053 q ha hb
    | true =>
      simp only [d17417, d28560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53052 q ha hb
  have h9 (q : Pattern) (ha : d17418 q = 1) (hb : d211415 q = 1) : d28561 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d28561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d28561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17419 q = 1) (hb : d211415 q = 1) : d28562 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d28562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d28562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17420 q = 1) (hb : d211415 q = 1) : d28563 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d28563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17420, d28563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171214 q = 1) (hb : d211415 q = 1) : d212485 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, d212485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171214, d212485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171215 q = 1) (hb : d211415 q = 1) : d212486 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171215, d212486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171215, d212486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53255 (p : Pattern) (ha : d171221 p = 1) (hb : d211415 p = 1) : d212492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171216 q = 1) (hb : d211415 q = 1) : d212487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171216, d212487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53254 q ha hb
    | true =>
      simp only [d171216, d212487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171217 q = 1) (hb : d211415 q = 1) : d212488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171217, d212488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171217, d212488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d211415 q = 1) : d28566 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d28566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53054 q ha hb
    | true =>
      simp only [d17423, d28566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d211415 q = 1) : d28567 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d28567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d28567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171218 q = 1) (hb : d211415 q = 1) : d212489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171218, d212489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171218, d212489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171219 q = 1) (hb : d211415 q = 1) : d212490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171219, d212490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171219, d212490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171220 q = 1) (hb : d211415 q = 1) : d212491 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171220, d212491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171220, d212491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171221 q = 1) (hb : d211415 q = 1) : d212492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171221, d212492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171221, d212492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53256 (p : Pattern) (ha : d171227 p = 1) (hb : d211415 p = 1) : d212498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171222 q = 1) (hb : d211415 q = 1) : d212493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171222, d212493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53255 q ha hb
    | true =>
      simp only [d171222, d212493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53055 q ha hb
  have h2 (q : Pattern) (ha : d171223 q = 1) (hb : d211415 q = 1) : d212494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171223, d212494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171223, d212494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171224 q = 1) (hb : d211415 q = 1) : d212495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171224, d212495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171224, d212495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171225 q = 1) (hb : d211415 q = 1) : d212496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171225, d212496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171225, d212496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171226 q = 1) (hb : d211415 q = 1) : d212497 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171226, d212497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171226, d212497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171227 q = 1) (hb : d211415 q = 1) : d212498 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171227, d212498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171227, d212498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53257 (p : Pattern) (ha : d171233 p = 1) (hb : d211415 p = 1) : d212504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17205 q = 1) (hb : d211415 q = 1) : d28224 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, d28224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53043 q ha hb
    | true =>
      simp only [d17205, d28224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53046 q ha hb
  have h2 (q : Pattern) (ha : d17206 q = 1) (hb : d211415 q = 1) : d28225 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, d28225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17206, d28225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171206 q = 1) (hb : d211415 q = 1) : d212477 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171206, d212477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171206, d212477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171207 q = 1) (hb : d211415 q = 1) : d212478 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171207, d212478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171207, d212478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171209 q = 1) (hb : d211415 q = 1) : d212480 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171209, d212480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171209, d212480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53253 q ha hb
  have h6 (q : Pattern) (ha : d171210 q = 1) (hb : d211415 q = 1) : d212481 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171210, d212481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171210, d212481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171211 q = 1) (hb : d211415 q = 1) : d212482 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171211, d212482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171211, d212482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171212 q = 1) (hb : d211415 q = 1) : d212483 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171212, d212483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171212, d212483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171213 q = 1) (hb : d211415 q = 1) : d212484 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171213, d212484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171213, d212484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171228 q = 1) (hb : d211415 q = 1) : d212499 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171228, d212499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171228, d212499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53256 q ha hb
  have h11 (q : Pattern) (ha : d171229 q = 1) (hb : d211415 q = 1) : d212500 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171229, d212500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171229, d212500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171230 q = 1) (hb : d211415 q = 1) : d212501 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171230, d212501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171230, d212501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171231 q = 1) (hb : d211415 q = 1) : d212502 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171231, d212502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171231, d212502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171232 q = 1) (hb : d211415 q = 1) : d212503 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171232, d212503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171232, d212503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171233 q = 1) (hb : d211415 q = 1) : d212504 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171233, d212504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171233, d212504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53258 (p : Pattern) (ha : d171239 p = 1) (hb : d211415 p = 1) : d212510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171234 q = 1) (hb : d211415 q = 1) : d212505 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171234, d212505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171234, d212505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53257 q ha hb
  have h2 (q : Pattern) (ha : d171235 q = 1) (hb : d211415 q = 1) : d212506 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171235, d212506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171235, d212506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171236 q = 1) (hb : d211415 q = 1) : d212507 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171236, d212507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171236, d212507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171237 q = 1) (hb : d211415 q = 1) : d212508 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171237, d212508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171237, d212508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171238 q = 1) (hb : d211415 q = 1) : d212509 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171238, d212509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171238, d212509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171239 q = 1) (hb : d211415 q = 1) : d212510 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171239, d212510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171239, d212510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53259 (p : Pattern) (ha : d171245 p = 1) (hb : d211415 p = 1) : d212516 p = 1 := by
  have h0 (q : Pattern) (ha : d171167 q = 1) (hb : d211415 q = 1) : d171167 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171202 q = 1) (hb : d211415 q = 1) : d212473 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171202, d212473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171202, d212473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53252 q ha hb
  have h3 (q : Pattern) (ha : d171203 q = 1) (hb : d211415 q = 1) : d212474 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171203, d212474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171203, d212474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171204 q = 1) (hb : d211415 q = 1) : d212475 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171204, d212475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171204, d212475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171205 q = 1) (hb : d211415 q = 1) : d212476 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171205, d212476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171205, d212476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171240 q = 1) (hb : d211415 q = 1) : d212511 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171240, d212511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171240, d212511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53258 q ha hb
  have h7 (q : Pattern) (ha : d171241 q = 1) (hb : d211415 q = 1) : d212512 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171241, d212512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171241, d212512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171242 q = 1) (hb : d211415 q = 1) : d212513 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171242, d212513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171242, d212513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d171243 q = 1) (hb : d211415 q = 1) : d212514 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171243, d212514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171243, d212514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171244 q = 1) (hb : d211415 q = 1) : d212515 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d171244, d212515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171244, d212515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d171245 q = 1) (hb : d211415 q = 1) : d212516 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d171245, d212516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171245, d212516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h11 p ha hb
theorem andIntro53260 (p : Pattern) (ha : d171251 p = 1) (hb : d211415 p = 1) : d212522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171246 q = 1) (hb : d211415 q = 1) : d212517 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d171246, d212517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53259 q ha hb
    | true =>
      simp only [d171246, d212517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171247 q = 1) (hb : d211415 q = 1) : d212518 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d171247, d212518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171247, d212518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171248 q = 1) (hb : d211415 q = 1) : d212519 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d171248, d212519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171248, d212519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171249 q = 1) (hb : d211415 q = 1) : d212520 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d171249, d212520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171249, d212520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171250 q = 1) (hb : d211415 q = 1) : d212521 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d171250, d212521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171250, d212521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171251 q = 1) (hb : d211415 q = 1) : d212522 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d171251, d212522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171251, d212522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53261 (p : Pattern) (ha : d171257 p = 1) (hb : d211415 p = 1) : d212528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171252 q = 1) (hb : d211415 q = 1) : d212523 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d171252, d212523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53260 q ha hb
    | true =>
      simp only [d171252, d212523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171253 q = 1) (hb : d211415 q = 1) : d212524 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d171253, d212524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171253, d212524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171254 q = 1) (hb : d211415 q = 1) : d212525 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d171254, d212525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171254, d212525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171255 q = 1) (hb : d211415 q = 1) : d212526 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d171255, d212526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171255, d212526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171256 q = 1) (hb : d211415 q = 1) : d212527 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d171256, d212527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171256, d212527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171257 q = 1) (hb : d211415 q = 1) : d212528 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d171257, d212528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171257, d212528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53262 (p : Pattern) (ha : d171263 p = 1) (hb : d211416 p = 1) : d212534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171258 q = 1) (hb : d211415 q = 1) : d212529 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d171258, d212529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53261 q ha hb
    | true =>
      simp only [d171258, d212529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171259 q = 1) (hb : d211415 q = 1) : d212530 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d171259, d212530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171259, d212530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171260 q = 1) (hb : d211415 q = 1) : d212531 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d171260, d212531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171260, d212531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171261 q = 1) (hb : d211415 q = 1) : d212532 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d171261, d212532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171261, d212532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171262 q = 1) (hb : d211415 q = 1) : d212533 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d171262, d212533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171262, d212533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d171263 q = 1) (hb : d211416 q = 1) : d212534 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d171263, d211416, d212534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171263, d211416, d212534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53263 (p : Pattern) (ha : d171269 p = 1) (hb : d211416 p = 1) : d212540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171264 q = 1) (hb : d211416 q = 1) : d212535 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d171264, d212535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53262 q ha hb
    | true =>
      simp only [d171264, d212535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171265 q = 1) (hb : d211416 q = 1) : d212536 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d171265, d212536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171265, d212536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171266 q = 1) (hb : d211416 q = 1) : d212537 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d171266, d212537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171266, d212537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171267 q = 1) (hb : d211416 q = 1) : d212538 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d171267, d212538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171267, d212538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171268 q = 1) (hb : d211416 q = 1) : d212539 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d171268, d212539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171268, d212539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171269 q = 1) (hb : d211416 q = 1) : d212540 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d171269, d212540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171269, d212540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53264 (p : Pattern) (ha : d171275 p = 1) (hb : d211416 p = 1) : d212546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171270 q = 1) (hb : d211416 q = 1) : d212541 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d171270, d212541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53263 q ha hb
    | true =>
      simp only [d171270, d212541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171271 q = 1) (hb : d211416 q = 1) : d212542 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d171271, d212542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171271, d212542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171272 q = 1) (hb : d211416 q = 1) : d212543 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d171272, d212543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171272, d212543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171273 q = 1) (hb : d211416 q = 1) : d212544 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d171273, d212544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171273, d212544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171274 q = 1) (hb : d211416 q = 1) : d212545 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d171274, d212545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171274, d212545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171275 q = 1) (hb : d211416 q = 1) : d212546 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d171275, d212546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171275, d212546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53265 (p : Pattern) (ha : d171281 p = 1) (hb : d211416 p = 1) : d212552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171276 q = 1) (hb : d211416 q = 1) : d212547 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d171276, d212547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53264 q ha hb
    | true =>
      simp only [d171276, d212547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171277 q = 1) (hb : d211416 q = 1) : d212548 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d171277, d212548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171277, d212548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171278 q = 1) (hb : d211416 q = 1) : d212549 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d171278, d212549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171278, d212549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171279 q = 1) (hb : d211416 q = 1) : d212550 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d171279, d212550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171279, d212550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171280 q = 1) (hb : d211416 q = 1) : d212551 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d171280, d212551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171280, d212551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171281 q = 1) (hb : d211416 q = 1) : d212552 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d171281, d212552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171281, d212552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53266 (p : Pattern) (ha : d171287 p = 1) (hb : d211416 p = 1) : d212558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171282 q = 1) (hb : d211416 q = 1) : d212553 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d171282, d212553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53265 q ha hb
    | true =>
      simp only [d171282, d212553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171283 q = 1) (hb : d211416 q = 1) : d212554 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d171283, d212554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171283, d212554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171284 q = 1) (hb : d211416 q = 1) : d212555 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d171284, d212555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171284, d212555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171285 q = 1) (hb : d211416 q = 1) : d212556 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d171285, d212556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171285, d212556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171286 q = 1) (hb : d211416 q = 1) : d212557 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d171286, d212557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171286, d212557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171287 q = 1) (hb : d211416 q = 1) : d212558 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d171287, d212558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171287, d212558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53267 (p : Pattern) (ha : d27599 p = 1) (hb : d211633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d211565 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d211613 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d27594 q = 1) (hb : d211530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27594, d211530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53117 q ha hb
    | true =>
      simp only [d27594, d211530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53118 q ha hb
  have h5 (q : Pattern) (ha : d27595 q = 1) (hb : d211614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27595, d211614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27595, d211614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d211629 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d27596 q = 1) (hb : d211630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27596, d211630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27596, d211630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27597 q = 1) (hb : d211631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27597, d211631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27597, d211631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d27598 q = 1) (hb : d211632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27598, d211632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27598, d211632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27599 q = 1) (hb : d211633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27599, d211633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27599, d211633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro53268 (p : Pattern) (ha : d27609 p = 1) (hb : d211655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211556 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211565 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d211613 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d27594 q = 1) (hb : d211530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27594, d211530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53117 q ha hb
    | true =>
      simp only [d27594, d211530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53118 q ha hb
  have h4 (q : Pattern) (ha : d27595 q = 1) (hb : d211614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27595, d211614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27595, d211614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d211629 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d27596 q = 1) (hb : d211630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27596, d211630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27596, d211630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27597 q = 1) (hb : d211631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27597, d211631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27597, d211631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27598 q = 1) (hb : d211632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27598, d211632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27598, d211632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d211639 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d211644 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d211647 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d27604 q = 1) (hb : d211540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27604, d211540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53120 q ha hb
    | true =>
      simp only [d27604, d211540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53121 q ha hb
  have h13 (q : Pattern) (ha : d27605 q = 1) (hb : d211648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27605, d211648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27605, d211648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d211651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d27606 q = 1) (hb : d211652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27606, d211652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d27606, d211652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d27607 q = 1) (hb : d211653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27607, d211653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27607, d211653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d27608 q = 1) (hb : d211654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27608, d211654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27608, d211654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d27609 q = 1) (hb : d211655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27609, d211655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27609, d211655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro53269 (p : Pattern) (ha : d211680 p = 1) (hb : d212441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211647 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27604 q = 1) (hb : d211540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27604, d211540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53120 q ha hb
    | true =>
      simp only [d27604, d211540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53121 q ha hb
  have h3 (q : Pattern) (ha : d27605 q = 1) (hb : d211648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27605, d211648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27605, d211648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d211651 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d27606 q = 1) (hb : d211652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27606, d211652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27606, d211652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27607 q = 1) (hb : d211678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27607, d211678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27607, d211678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27608 q = 1) (hb : d211679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27608, d211679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27608, d211679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211680 q = 1) (hb : d212441 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211680, d212441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211680, d212441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro53270 (p : Pattern) (ha : d211793 p = 1) (hb : d212448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27923 q = 1) (hb : d211742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27923, d211742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53158 q ha hb
    | true =>
      simp only [d27923, d211742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53128 q ha hb
  have h2 (q : Pattern) (ha : d27924 q = 1) (hb : d211743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27924, d211743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27924, d211743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27925 q = 1) (hb : d211744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27925, d211744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27925, d211744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27937 q = 1) (hb : d211756 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27937, d211756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53128 q ha hb
    | true =>
      simp only [d27937, d211756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53160 q ha hb
  have h5 (q : Pattern) (ha : d27938 q = 1) (hb : d211757 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27938, d211757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27938, d211757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27939 q = 1) (hb : d211758 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27939, d211758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27939, d211758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27940 q = 1) (hb : d211759 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27940, d211759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27940, d211759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27960 q = 1) (hb : d211779 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27960, d211779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53128 q ha hb
    | true =>
      simp only [d27960, d211779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53129 q ha hb
  have h9 (q : Pattern) (ha : d27961 q = 1) (hb : d211780 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27961, d211780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27961, d211780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27962 q = 1) (hb : d211781 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27962, d211781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27962, d211781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27963 q = 1) (hb : d211782 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27963, d211782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27963, d211782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d211792 q = 1) (hb : d212447 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d211792, d212447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d211792, d212447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d211793 q = 1) (hb : d212448 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d211793, d212448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211793, d212448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro53271 (p : Pattern) (ha : d211799 p = 1) (hb : d212454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211794 q = 1) (hb : d212449 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d211794, d212449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53270 q ha hb
    | true =>
      simp only [d211794, d212449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d211795 q = 1) (hb : d212450 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d211795, d212450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211795, d212450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27966 q = 1) (hb : d211785 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27966, d211785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53130 q ha hb
    | true =>
      simp only [d27966, d211785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27967 q = 1) (hb : d211786 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27967, d211786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27967, d211786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211796 q = 1) (hb : d212451 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d211796, d212451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211796, d212451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211797 q = 1) (hb : d212452 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d211797, d212452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211797, d212452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d211798 q = 1) (hb : d212453 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d211798, d212453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211798, d212453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d211799 q = 1) (hb : d212454 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d211799, d212454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211799, d212454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro53272 (p : Pattern) (ha : d211824 p = 1) (hb : d212460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211791 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d211804 q = 1) (hb : d212455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d211804, d212455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53271 q ha hb
    | true =>
      simp only [d211804, d212455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53131 q hb ha
  have h3 (q : Pattern) (ha : d211805 q = 1) (hb : d212456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211805, d212456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211805, d212456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d211820 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211821 q = 1) (hb : d212457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211821, d212457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211821, d212457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211822 q = 1) (hb : d212458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211822, d212458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211822, d212458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211823 q = 1) (hb : d212459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211823, d212459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211823, d212459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211824 q = 1) (hb : d212460 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211824, d212460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211824, d212460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53273 (p : Pattern) (ha : d211837 p = 1) (hb : d212466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211548 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27610 q = 1) (hb : d211656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27610, d211656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53267 q ha hb
    | true =>
      simp only [d27610, d211656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53268 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d211674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d27611 q = 1) (hb : d211675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27611, d211675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27611, d211675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211676 q = 1) (hb : d212439 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211676, d212439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211676, d212439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211677 q = 1) (hb : d212440 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211677, d212440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211677, d212440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211681 q = 1) (hb : d212442 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211681, d212442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211681, d212442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53269 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d211683 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211684 q = 1) (hb : d212443 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211684, d212443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211684, d212443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211685 q = 1) (hb : d212444 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211685, d212444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211685, d212444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d211686 q = 1) (hb : d212445 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211686, d212445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211686, d212445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d211687 q = 1) (hb : d212446 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211687, d212446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211687, d212446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211825 q = 1) (hb : d212461 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211825, d212461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211825, d212461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53272 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d211832 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211833 q = 1) (hb : d212462 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211833, d212462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211833, d212462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211834 q = 1) (hb : d212463 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211834, d212463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211834, d212463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d211835 q = 1) (hb : d212464 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211835, d212464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211835, d212464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d211836 q = 1) (hb : d212465 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211836, d212465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211836, d212465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d211837 q = 1) (hb : d212466 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211837, d212466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211837, d212466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro53274 (p : Pattern) (ha : d211843 p = 1) (hb : d212472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211838 q = 1) (hb : d212467 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211838, d212467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211838, d212467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53273 q ha hb
  have h2 (q : Pattern) (ha : d211839 q = 1) (hb : d212468 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211839, d212468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211839, d212468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211840 q = 1) (hb : d212469 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211840, d212469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211840, d212469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211841 q = 1) (hb : d212470 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211841, d212470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211841, d212470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211842 q = 1) (hb : d212471 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211842, d212471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211842, d212471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211843 q = 1) (hb : d212472 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211843, d212472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211843, d212472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53275 (p : Pattern) (ha : d28213 p = 1) (hb : d212055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211987 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d211996 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d212035 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28208 q = 1) (hb : d211961 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28208, d211961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53186 q ha hb
    | true =>
      simp only [d28208, d211961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53187 q ha hb
  have h5 (q : Pattern) (ha : d28209 q = 1) (hb : d212036 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28209, d212036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28209, d212036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d212051 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28210 q = 1) (hb : d212052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28210, d212052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28210, d212052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28211 q = 1) (hb : d212053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28211, d212053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28211, d212053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28212 q = 1) (hb : d212054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28212, d212054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28212, d212054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28213 q = 1) (hb : d212055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28213, d212055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28213, d212055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro53276 (p : Pattern) (ha : d28223 p = 1) (hb : d212077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211987 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d212035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d28208 q = 1) (hb : d211961 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28208, d211961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53186 q ha hb
    | true =>
      simp only [d28208, d211961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53187 q ha hb
  have h4 (q : Pattern) (ha : d28209 q = 1) (hb : d212036 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28209, d212036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28209, d212036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d212051 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d28210 q = 1) (hb : d212052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28210, d212052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28210, d212052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28211 q = 1) (hb : d212053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28211, d212053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28211, d212053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28212 q = 1) (hb : d212054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28212, d212054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28212, d212054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d212061 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d212066 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d212069 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d28218 q = 1) (hb : d211971 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28218, d211971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53189 q ha hb
    | true =>
      simp only [d28218, d211971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53190 q ha hb
  have h13 (q : Pattern) (ha : d28219 q = 1) (hb : d212070 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28219, d212070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28219, d212070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d212073 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d28220 q = 1) (hb : d212074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28220, d212074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28220, d212074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28221 q = 1) (hb : d212075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28221, d212075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28221, d212075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28222 q = 1) (hb : d212076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28222, d212076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28222, d212076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d28223 q = 1) (hb : d212077 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28223, d212077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28223, d212077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro53277 (p : Pattern) (ha : d212102 p = 1) (hb : d212479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d212069 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28218 q = 1) (hb : d211971 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28218, d211971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53189 q ha hb
    | true =>
      simp only [d28218, d211971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53190 q ha hb
  have h3 (q : Pattern) (ha : d28219 q = 1) (hb : d212070 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28219, d212070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28219, d212070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d212073 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28220 q = 1) (hb : d212074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28220, d212074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28220, d212074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28221 q = 1) (hb : d212100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28221, d212100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28221, d212100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28222 q = 1) (hb : d212101 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28222, d212101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28222, d212101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212102 q = 1) (hb : d212479 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212102, d212479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212102, d212479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro53278 (p : Pattern) (ha : d212210 p = 1) (hb : d212486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28523 q = 1) (hb : d212159 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28523, d212159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53226 q ha hb
    | true =>
      simp only [d28523, d212159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53197 q ha hb
  have h2 (q : Pattern) (ha : d28524 q = 1) (hb : d212160 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28524, d212160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28524, d212160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28525 q = 1) (hb : d212161 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28525, d212161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28525, d212161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28537 q = 1) (hb : d212173 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28537, d212173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53197 q ha hb
    | true =>
      simp only [d28537, d212173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53228 q ha hb
  have h5 (q : Pattern) (ha : d28538 q = 1) (hb : d212174 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28538, d212174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28538, d212174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28539 q = 1) (hb : d212175 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28539, d212175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28539, d212175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28540 q = 1) (hb : d212176 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28540, d212176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28540, d212176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28560 q = 1) (hb : d212196 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28560, d212196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53197 q ha hb
    | true =>
      simp only [d28560, d212196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53198 q ha hb
  have h9 (q : Pattern) (ha : d28561 q = 1) (hb : d212197 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28561, d212197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28561, d212197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28562 q = 1) (hb : d212198 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28562, d212198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28562, d212198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28563 q = 1) (hb : d212199 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28563, d212199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28563, d212199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d212209 q = 1) (hb : d212485 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212209, d212485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d212209, d212485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d212210 q = 1) (hb : d212486 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212210, d212486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212210, d212486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro53279 (p : Pattern) (ha : d212216 p = 1) (hb : d212492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212211 q = 1) (hb : d212487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212211, d212487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53278 q ha hb
    | true =>
      simp only [d212211, d212487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212212 q = 1) (hb : d212488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212212, d212488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212212, d212488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28566 q = 1) (hb : d212202 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28566, d212202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53199 q ha hb
    | true =>
      simp only [d28566, d212202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28567 q = 1) (hb : d212203 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28567, d212203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28567, d212203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212213 q = 1) (hb : d212489 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212213, d212489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212213, d212489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212214 q = 1) (hb : d212490 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212214, d212490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212214, d212490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d212215 q = 1) (hb : d212491 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212215, d212491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212215, d212491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d212216 q = 1) (hb : d212492 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212216, d212492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212216, d212492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro53280 (p : Pattern) (ha : d212241 p = 1) (hb : d212498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d212208 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d212221 q = 1) (hb : d212493 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212221, d212493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53279 q ha hb
    | true =>
      simp only [d212221, d212493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53200 q hb ha
  have h3 (q : Pattern) (ha : d212222 q = 1) (hb : d212494 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212222, d212494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212222, d212494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d212237 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212238 q = 1) (hb : d212495 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212238, d212495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212238, d212495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212239 q = 1) (hb : d212496 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212239, d212496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212239, d212496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212240 q = 1) (hb : d212497 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212240, d212497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212240, d212497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212241 q = 1) (hb : d212498 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212241, d212498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212241, d212498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53281 (p : Pattern) (ha : d212254 p = 1) (hb : d212504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211979 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28224 q = 1) (hb : d212078 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28224, d212078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53275 q ha hb
    | true =>
      simp only [d28224, d212078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53276 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d212096 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d28225 q = 1) (hb : d212097 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28225, d212097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28225, d212097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212098 q = 1) (hb : d212477 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212098, d212477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d212098, d212477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212099 q = 1) (hb : d212478 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212099, d212478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212099, d212478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212103 q = 1) (hb : d212480 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212103, d212480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d212103, d212480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53277 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d212105 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d212106 q = 1) (hb : d212481 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212106, d212481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212106, d212481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d212107 q = 1) (hb : d212482 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212107, d212482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212107, d212482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d212108 q = 1) (hb : d212483 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212108, d212483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212108, d212483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d212109 q = 1) (hb : d212484 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212109, d212484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212109, d212484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212242 q = 1) (hb : d212499 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212242, d212499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d212242, d212499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53280 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d212249 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d212250 q = 1) (hb : d212500 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212250, d212500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212250, d212500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d212251 q = 1) (hb : d212501 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212251, d212501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212251, d212501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d212252 q = 1) (hb : d212502 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212252, d212502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d212252, d212502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d212253 q = 1) (hb : d212503 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212253, d212503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d212253, d212503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d212254 q = 1) (hb : d212504 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212254, d212504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212254, d212504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro53282 (p : Pattern) (ha : d212260 p = 1) (hb : d212510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212255 q = 1) (hb : d212505 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212255, d212505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212255, d212505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53281 q ha hb
  have h2 (q : Pattern) (ha : d212256 q = 1) (hb : d212506 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212256, d212506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212256, d212506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212257 q = 1) (hb : d212507 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212257, d212507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212257, d212507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d212258 q = 1) (hb : d212508 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212258, d212508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212258, d212508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212259 q = 1) (hb : d212509 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212259, d212509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212259, d212509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212260 q = 1) (hb : d212510 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212260, d212510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212260, d212510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53283 (p : Pattern) (ha : d212266 p = 1) (hb : d212516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d127103 q = 1) (hb : d171102 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127103, d171102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38084 q hb ha
    | true =>
      simp only [d127103, d171102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38090 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127274 q = 1) (hb : d171129 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127274, d171129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127274, d171129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38096 q ha hb
  have h3 (q : Pattern) (ha : d127275 q = 1) (hb : d171130 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127275, d171130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d127275, d171130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127558 q = 1) (hb : d171165 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127558, d171165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127558, d171165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38104 q ha hb
  have h5 (q : Pattern) (ha : d127559 q = 1) (hb : d171166 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127559, d171166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127559, d171166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127560 q = 1) (hb : d171167 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127560, d171167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127560, d171167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211844 q = 1) (hb : d212473 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211844, d212473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211844, d212473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53274 q ha hb
  have h8 (q : Pattern) (ha : d211845 q = 1) (hb : d212474 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211845, d212474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211845, d212474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211846 q = 1) (hb : d212475 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d211846, d212475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211846, d212475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211847 q = 1) (hb : d212476 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d211847, d212476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211847, d212476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d212261 q = 1) (hb : d212511 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212261, d212511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212261, d212511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53282 q ha hb
  have h12 (q : Pattern) (ha : d212262 q = 1) (hb : d212512 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212262, d212512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212262, d212512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212263 q = 1) (hb : d212513 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212263, d212513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212263, d212513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d212264 q = 1) (hb : d212514 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212264, d212514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212264, d212514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d212265 q = 1) (hb : d212515 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d212265, d212515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212265, d212515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d212266 q = 1) (hb : d212516 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d212266, d212516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212266, d212516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro53284 (p : Pattern) (ha : d212272 p = 1) (hb : d212522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212267 q = 1) (hb : d212517 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d212267, d212517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53283 q ha hb
    | true =>
      simp only [d212267, d212517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212268 q = 1) (hb : d212518 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d212268, d212518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212268, d212518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212269 q = 1) (hb : d212519 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d212269, d212519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212269, d212519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212270 q = 1) (hb : d212520 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d212270, d212520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212270, d212520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212271 q = 1) (hb : d212521 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d212271, d212521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212271, d212521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212272 q = 1) (hb : d212522 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d212272, d212522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212272, d212522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro53285 (p : Pattern) (ha : d212278 p = 1) (hb : d212528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212273 q = 1) (hb : d212523 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d212273, d212523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53284 q ha hb
    | true =>
      simp only [d212273, d212523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212274 q = 1) (hb : d212524 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d212274, d212524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212274, d212524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212275 q = 1) (hb : d212525 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d212275, d212525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212275, d212525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212276 q = 1) (hb : d212526 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d212276, d212526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212276, d212526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212277 q = 1) (hb : d212527 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d212277, d212527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212277, d212527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212278 q = 1) (hb : d212528 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d212278, d212528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212278, d212528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro53286 (p : Pattern) (ha : d212284 p = 1) (hb : d212534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212279 q = 1) (hb : d212529 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d212279, d212529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53285 q ha hb
    | true =>
      simp only [d212279, d212529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212280 q = 1) (hb : d212530 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d212280, d212530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212280, d212530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212281 q = 1) (hb : d212531 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d212281, d212531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212281, d212531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212282 q = 1) (hb : d212532 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d212282, d212532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212282, d212532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212283 q = 1) (hb : d212533 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d212283, d212533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212283, d212533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212284 q = 1) (hb : d212534 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d212284, d212534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212284, d212534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro53287 (p : Pattern) (ha : d212290 p = 1) (hb : d212540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212285 q = 1) (hb : d212535 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d212285, d212535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53286 q ha hb
    | true =>
      simp only [d212285, d212535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212286 q = 1) (hb : d212536 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d212286, d212536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212286, d212536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212287 q = 1) (hb : d212537 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d212287, d212537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212287, d212537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212288 q = 1) (hb : d212538 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d212288, d212538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212288, d212538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212289 q = 1) (hb : d212539 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d212289, d212539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212289, d212539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212290 q = 1) (hb : d212540 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d212290, d212540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212290, d212540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro53288 (p : Pattern) (ha : d212296 p = 1) (hb : d212546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212291 q = 1) (hb : d212541 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d212291, d212541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53287 q ha hb
    | true =>
      simp only [d212291, d212541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212292 q = 1) (hb : d212542 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d212292, d212542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212292, d212542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212293 q = 1) (hb : d212543 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d212293, d212543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212293, d212543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212294 q = 1) (hb : d212544 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d212294, d212544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212294, d212544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212295 q = 1) (hb : d212545 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d212295, d212545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212295, d212545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212296 q = 1) (hb : d212546 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d212296, d212546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212296, d212546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro53289 (p : Pattern) (ha : d212302 p = 1) (hb : d212552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212297 q = 1) (hb : d212547 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d212297, d212547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53288 q ha hb
    | true =>
      simp only [d212297, d212547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212298 q = 1) (hb : d212548 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d212298, d212548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212298, d212548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212299 q = 1) (hb : d212549 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d212299, d212549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212299, d212549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212300 q = 1) (hb : d212550 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d212300, d212550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212300, d212550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212301 q = 1) (hb : d212551 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d212301, d212551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212301, d212551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212302 q = 1) (hb : d212552 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d212302, d212552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212302, d212552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro53290 (p : Pattern) (ha : d212308 p = 1) (hb : d212558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212303 q = 1) (hb : d212553 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d212303, d212553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53289 q ha hb
    | true =>
      simp only [d212303, d212553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212304 q = 1) (hb : d212554 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d212304, d212554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212304, d212554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212305 q = 1) (hb : d212555 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d212305, d212555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212305, d212555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212306 q = 1) (hb : d212556 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d212306, d212556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212306, d212556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212307 q = 1) (hb : d212557 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d212307, d212557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212307, d212557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212308 q = 1) (hb : d212558 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d212308, d212558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212308, d212558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro53291 (p : Pattern) (ha : d27599 p = 1) (hb : d212313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27629 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d27677 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d27594 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d27595 q = 1) (hb : d212309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27595, d212309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27595, d212309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d27807 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d27596 q = 1) (hb : d212310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27596, d212310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27596, d212310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27597 q = 1) (hb : d212311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27597, d212311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27597, d212311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d27598 q = 1) (hb : d212312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27598, d212312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27598, d212312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27599 q = 1) (hb : d212313 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27599, d212313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27599, d212313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro53292 (p : Pattern) (ha : d27609 p = 1) (hb : d212318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27620 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27677 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d27594 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d27595 q = 1) (hb : d212309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27595, d212309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27595, d212309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d27807 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d27596 q = 1) (hb : d212310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27596, d212310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27596, d212310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27597 q = 1) (hb : d212311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27597, d212311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27597, d212311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27598 q = 1) (hb : d212312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27598, d212312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27598, d212312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d27817 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d27822 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d27825 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d27604 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d27605 q = 1) (hb : d212314 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27605, d212314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27605, d212314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27832 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d27606 q = 1) (hb : d212315 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27606, d212315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d27606, d212315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d27607 q = 1) (hb : d212316 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27607, d212316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27607, d212316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d27608 q = 1) (hb : d212317 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27608, d212317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27608, d212317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d27609 q = 1) (hb : d212318 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27609, d212318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27609, d212318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro53293 (p : Pattern) (ha : d212325 p = 1) (hb : d212441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27604 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d27605 q = 1) (hb : d212314 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27605, d212314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27605, d212314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d27832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d27606 q = 1) (hb : d212315 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27606, d212315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27606, d212315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27607 q = 1) (hb : d212323 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27607, d212323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27607, d212323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27608 q = 1) (hb : d212324 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27608, d212324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27608, d212324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212325 q = 1) (hb : d212441 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212325, d212441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212325, d212441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro53294 (p : Pattern) (ha : d212335 p = 1) (hb : d212460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d212455 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d212331 q = 1) (hb : d212456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212331, d212456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212331, d212456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28063 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212332 q = 1) (hb : d212457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212332, d212457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212332, d212457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212333 q = 1) (hb : d212458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212333, d212458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212333, d212458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212334 q = 1) (hb : d212459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212334, d212459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212334, d212459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212335 q = 1) (hb : d212460 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212335, d212460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212335, d212460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53295 (p : Pattern) (ha : d212341 p = 1) (hb : d212466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27612 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27610 q = 1) (hb : d212319 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27610, d212319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53291 q ha hb
    | true =>
      simp only [d27610, d212319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53292 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27855 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d27611 q = 1) (hb : d212320 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27611, d212320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27611, d212320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212321 q = 1) (hb : d212439 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212321, d212439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d212321, d212439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212322 q = 1) (hb : d212440 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212322, d212440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212322, d212440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212326 q = 1) (hb : d212442 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212326, d212442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212326, d212442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53293 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d27864 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d212327 q = 1) (hb : d212443 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212327, d212443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212327, d212443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d212328 q = 1) (hb : d212444 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212328, d212444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212328, d212444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d212329 q = 1) (hb : d212445 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212329, d212445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212329, d212445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d212330 q = 1) (hb : d212446 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212330, d212446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212330, d212446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212336 q = 1) (hb : d212461 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212336, d212461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212336, d212461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53294 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d28079 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d212337 q = 1) (hb : d212462 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212337, d212462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212337, d212462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d212338 q = 1) (hb : d212463 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212338, d212463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212338, d212463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d212339 q = 1) (hb : d212464 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212339, d212464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d212339, d212464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d212340 q = 1) (hb : d212465 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212340, d212465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d212340, d212465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d212341 q = 1) (hb : d212466 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212341, d212466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212341, d212466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro53296 (p : Pattern) (ha : d212347 p = 1) (hb : d212472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212342 q = 1) (hb : d212467 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212342, d212467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212342, d212467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53295 q ha hb
  have h2 (q : Pattern) (ha : d212343 q = 1) (hb : d212468 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212343, d212468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212343, d212468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212344 q = 1) (hb : d212469 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212344, d212469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212344, d212469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d212345 q = 1) (hb : d212470 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212345, d212470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212345, d212470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212346 q = 1) (hb : d212471 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212346, d212471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212346, d212471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212347 q = 1) (hb : d212472 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212347, d212472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212347, d212472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53297 (p : Pattern) (ha : d28213 p = 1) (hb : d212356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28243 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d28282 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28208 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28209 q = 1) (hb : d212352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28209, d212352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28209, d212352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d28412 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28210 q = 1) (hb : d212353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28210, d212353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28210, d212353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28211 q = 1) (hb : d212354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28211, d212354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28211, d212354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28212 q = 1) (hb : d212355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28212, d212355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28212, d212355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28213 q = 1) (hb : d212356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28213, d212356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28213, d212356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro53298 (p : Pattern) (ha : d28223 p = 1) (hb : d212361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28234 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28282 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d28208 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28209 q = 1) (hb : d212352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28209, d212352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28209, d212352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d28412 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d28210 q = 1) (hb : d212353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28210, d212353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28210, d212353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28211 q = 1) (hb : d212354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28211, d212354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28211, d212354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28212 q = 1) (hb : d212355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28212, d212355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28212, d212355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d28422 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d28427 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d28430 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d28218 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d28219 q = 1) (hb : d212357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28219, d212357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28219, d212357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d28437 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d28220 q = 1) (hb : d212358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28220, d212358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28220, d212358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28221 q = 1) (hb : d212359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28221, d212359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28221, d212359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28222 q = 1) (hb : d212360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28222, d212360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28222, d212360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d28223 q = 1) (hb : d212361 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28223, d212361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28223, d212361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro53299 (p : Pattern) (ha : d212368 p = 1) (hb : d212479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28430 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28218 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d28219 q = 1) (hb : d212357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28219, d212357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28219, d212357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28437 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28220 q = 1) (hb : d212358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28220, d212358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28220, d212358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28221 q = 1) (hb : d212366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28221, d212366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28221, d212366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28222 q = 1) (hb : d212367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28222, d212367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28222, d212367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212368 q = 1) (hb : d212479 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212368, d212479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212368, d212479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro53300 (p : Pattern) (ha : d212378 p = 1) (hb : d212498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d212493 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d212374 q = 1) (hb : d212494 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212374, d212494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212374, d212494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28663 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212375 q = 1) (hb : d212495 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212375, d212495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212375, d212495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212376 q = 1) (hb : d212496 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212376, d212496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212376, d212496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212377 q = 1) (hb : d212497 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212377, d212497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212377, d212497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212378 q = 1) (hb : d212498 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212378, d212498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212378, d212498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53301 (p : Pattern) (ha : d212384 p = 1) (hb : d212504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28226 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28224 q = 1) (hb : d212362 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28224, d212362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53297 q ha hb
    | true =>
      simp only [d28224, d212362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53298 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28460 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d28225 q = 1) (hb : d212363 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28225, d212363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28225, d212363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212364 q = 1) (hb : d212477 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212364, d212477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d212364, d212477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212365 q = 1) (hb : d212478 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212365, d212478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212365, d212478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212369 q = 1) (hb : d212480 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212369, d212480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212369, d212480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53299 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d28469 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d212370 q = 1) (hb : d212481 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212370, d212481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212370, d212481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d212371 q = 1) (hb : d212482 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212371, d212482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212371, d212482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d212372 q = 1) (hb : d212483 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212372, d212483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212372, d212483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d212373 q = 1) (hb : d212484 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212373, d212484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212373, d212484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212379 q = 1) (hb : d212499 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212379, d212499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212379, d212499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53300 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d28679 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d212380 q = 1) (hb : d212500 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212380, d212500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212380, d212500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d212381 q = 1) (hb : d212501 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212381, d212501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212381, d212501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d212382 q = 1) (hb : d212502 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212382, d212502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d212382, d212502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d212383 q = 1) (hb : d212503 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212383, d212503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d212383, d212503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d212384 q = 1) (hb : d212504 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212384, d212504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212384, d212504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro53302 (p : Pattern) (ha : d212390 p = 1) (hb : d212510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212385 q = 1) (hb : d212505 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212385, d212505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212385, d212505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53301 q ha hb
  have h2 (q : Pattern) (ha : d212386 q = 1) (hb : d212506 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212386, d212506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212386, d212506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212387 q = 1) (hb : d212507 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212387, d212507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212387, d212507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d212388 q = 1) (hb : d212508 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212388, d212508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212388, d212508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212389 q = 1) (hb : d212509 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212389, d212509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212389, d212509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212390 q = 1) (hb : d212510 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212390, d212510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212390, d212510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53303 (p : Pattern) (ha : d212396 p = 1) (hb : d212516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d171102 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d171102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38134 q hb ha
    | true =>
      simp only [d128269, d171102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38140 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d171129 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d171129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, d171129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38146 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d171130 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d171130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d171130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d171165 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d171165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, d171165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38152 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d171166 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d171166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, d171166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d171167 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d171167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d171167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212348 q = 1) (hb : d212473 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212348, d212473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212348, d212473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53296 q ha hb
  have h8 (q : Pattern) (ha : d212349 q = 1) (hb : d212474 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212349, d212474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212349, d212474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d212350 q = 1) (hb : d212475 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212350, d212475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212350, d212475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212351 q = 1) (hb : d212476 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212351, d212476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212351, d212476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d212391 q = 1) (hb : d212511 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212391, d212511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212391, d212511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53302 q ha hb
  have h12 (q : Pattern) (ha : d212392 q = 1) (hb : d212512 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212392, d212512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212392, d212512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212393 q = 1) (hb : d212513 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212393, d212513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212393, d212513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d212394 q = 1) (hb : d212514 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212394, d212514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212394, d212514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d212395 q = 1) (hb : d212515 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d212395, d212515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212395, d212515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d212396 q = 1) (hb : d212516 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d212396, d212516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212396, d212516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro53304 (p : Pattern) (ha : d212402 p = 1) (hb : d212522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212397 q = 1) (hb : d212517 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d212397, d212517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53303 q ha hb
    | true =>
      simp only [d212397, d212517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212398 q = 1) (hb : d212518 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d212398, d212518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212398, d212518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212399 q = 1) (hb : d212519 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d212399, d212519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212399, d212519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212400 q = 1) (hb : d212520 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d212400, d212520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212400, d212520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212401 q = 1) (hb : d212521 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d212401, d212521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212401, d212521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212402 q = 1) (hb : d212522 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d212402, d212522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212402, d212522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53305 (p : Pattern) (ha : d212408 p = 1) (hb : d212528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212403 q = 1) (hb : d212523 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d212403, d212523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53304 q ha hb
    | true =>
      simp only [d212403, d212523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212404 q = 1) (hb : d212524 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d212404, d212524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212404, d212524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212405 q = 1) (hb : d212525 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d212405, d212525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212405, d212525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212406 q = 1) (hb : d212526 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d212406, d212526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212406, d212526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212407 q = 1) (hb : d212527 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d212407, d212527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212407, d212527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212408 q = 1) (hb : d212528 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d212408, d212528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212408, d212528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53306 (p : Pattern) (ha : d212414 p = 1) (hb : d212534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212409 q = 1) (hb : d212529 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d212409, d212529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53305 q ha hb
    | true =>
      simp only [d212409, d212529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212410 q = 1) (hb : d212530 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d212410, d212530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212410, d212530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212411 q = 1) (hb : d212531 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d212411, d212531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212411, d212531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212412 q = 1) (hb : d212532 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d212412, d212532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212412, d212532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212413 q = 1) (hb : d212533 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d212413, d212533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212413, d212533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212414 q = 1) (hb : d212534 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d212414, d212534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212414, d212534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53307 (p : Pattern) (ha : d212420 p = 1) (hb : d212540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212415 q = 1) (hb : d212535 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d212415, d212535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53306 q ha hb
    | true =>
      simp only [d212415, d212535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212416 q = 1) (hb : d212536 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d212416, d212536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212416, d212536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212417 q = 1) (hb : d212537 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d212417, d212537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212417, d212537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212418 q = 1) (hb : d212538 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d212418, d212538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212418, d212538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212419 q = 1) (hb : d212539 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d212419, d212539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212419, d212539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212420 q = 1) (hb : d212540 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d212420, d212540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212420, d212540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53308 (p : Pattern) (ha : d212426 p = 1) (hb : d212546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212421 q = 1) (hb : d212541 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d212421, d212541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53307 q ha hb
    | true =>
      simp only [d212421, d212541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212422 q = 1) (hb : d212542 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d212422, d212542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212422, d212542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212423 q = 1) (hb : d212543 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d212423, d212543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212423, d212543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212424 q = 1) (hb : d212544 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d212424, d212544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212424, d212544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212425 q = 1) (hb : d212545 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d212425, d212545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212425, d212545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212426 q = 1) (hb : d212546 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d212426, d212546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212426, d212546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53309 (p : Pattern) (ha : d212432 p = 1) (hb : d212552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212427 q = 1) (hb : d212547 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d212427, d212547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53308 q ha hb
    | true =>
      simp only [d212427, d212547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212428 q = 1) (hb : d212548 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d212428, d212548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212428, d212548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212429 q = 1) (hb : d212549 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d212429, d212549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212429, d212549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212430 q = 1) (hb : d212550 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d212430, d212550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212430, d212550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212431 q = 1) (hb : d212551 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d212431, d212551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212431, d212551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212432 q = 1) (hb : d212552 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d212432, d212552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212432, d212552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53310 (p : Pattern) (ha : d212438 p = 1) (hb : d212558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212433 q = 1) (hb : d212553 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d212433, d212553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53309 q ha hb
    | true =>
      simp only [d212433, d212553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212434 q = 1) (hb : d212554 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d212434, d212554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212434, d212554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212435 q = 1) (hb : d212555 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d212435, d212555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212435, d212555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212436 q = 1) (hb : d212556 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d212436, d212556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212436, d212556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212437 q = 1) (hb : d212557 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d212437, d212557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212437, d212557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212438 q = 1) (hb : d212558 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d212438, d212558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212438, d212558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53311 (p : Pattern) (ha : d138 p = 1) (hb : d198467 p = 1) : d25690 p = 1 := by
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
  have h3 (q : Pattern) (ha : d21 q = 1) (hb : d152852 q = 1) : d21 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d136 q = 1) (hb : d152852 q = 1) : d25102 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d137 q = 1) (hb : d152852 q = 1) : d25103 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d23 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d138 q = 1) (hb : d198467 q = 1) : d25690 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d198467, d25690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d138, d198467, d25690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro53312 (p : Pattern) (ha : d144 p = 1) (hb : d198467 p = 1) : d200251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53311 q ha hb
    | true =>
      simp only [d139, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d198467 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d198467 q = 1) : d200250 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d200250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d200250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d198467 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d144 q = 1) (hb : d198467 q = 1) : d200251 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d200251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144, d200251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53313 (p : Pattern) (ha : d150 p = 1) (hb : d198467 p = 1) : d200257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53312 q ha hb
    | true =>
      simp only [d145, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d198467 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d198467 q = 1) : d200255 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d198467 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d198467 q = 1) : d200256 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d200256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d200256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d198467 q = 1) : d200257 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d200257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d200257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro53314 (p : Pattern) (ha : d203 p = 1) (hb : d198467 p = 1) : d200270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53313 q ha hb
    | true =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d198467 q = 1) : d200262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d198467 q = 1) : d200270 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d200270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d200270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro53315 (p : Pattern) (ha : d4349 p = 1) (hb : d198467 p = 1) : d200283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53314 q ha hb
    | true =>
      simp only [d204, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d198467 q = 1) : d200272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d198467 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d198467 q = 1) : d200273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d198467 q = 1) : d200281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d200281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d200281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d198467 q = 1) : d200282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d200282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d200282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d198467 q = 1) : d200283 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d200283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d200283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53316 (p : Pattern) (ha : d231 p = 1) (hb : d198467 p = 1) : d200290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53311 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53311 q ha hb
    | true =>
      simp only [d139, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d198467 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d198467 q = 1) : d200289 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d200289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d200289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d198467 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d231 q = 1) (hb : d198467 q = 1) : d200290 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d200290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231, d200290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro53317 (p : Pattern) (ha : d237 p = 1) (hb : d198467 p = 1) : d200296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53316 q ha hb
    | true =>
      simp only [d232, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d198467 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d198467 q = 1) : d200294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d198467 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d198467 q = 1) : d200295 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d200295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d200295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d198467 q = 1) : d200296 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d200296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d200296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro53318 (p : Pattern) (ha : d243 p = 1) (hb : d198467 p = 1) : d200302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d198467 q = 1) : d200297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53317 q ha hb
    | true =>
      simp only [d238, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d198467 q = 1) : d200298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d198467 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d198467 q = 1) : d200299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d200299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d200299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d198467 q = 1) : d200300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d200300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d200300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d198467 q = 1) : d200301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d200301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d200301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d198467 q = 1) : d200302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d200302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d200302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro53319 (p : Pattern) (ha : d4359 p = 1) (hb : d198467 p = 1) : d200308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d198467 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d198467 q = 1) : d200303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53318 q ha hb
    | true =>
      simp only [d244, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d198467 q = 1) : d200304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d200304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d200304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d198467 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d198467 q = 1) : d200305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d200305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d200305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d198467 q = 1) : d200306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d200306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d200306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d198467 q = 1) : d200307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d200307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d200307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d198467 q = 1) : d200308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d200308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d200308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53320 (p : Pattern) (ha : d156 p = 1) (hb : d198467 p = 1) : d200263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53313 q ha hb
    | true =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d198467 q = 1) : d200262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d198467 q = 1) : d200263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d200263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d200263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53321 (p : Pattern) (ha : d51643 p = 1) (hb : d198467 p = 1) : d200269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d198467 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d198467 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53320 q ha hb
    | true =>
      simp only [d157, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d198467 q = 1) : d200265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d198467 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d198467 q = 1) : d200266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d198467 q = 1) : d200267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d198467 q = 1) : d200268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d198467 q = 1) : d200269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d200269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d200269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro53322 (p : Pattern) (ha : d51646 p = 1) (hb : d198467 p = 1) : d200276 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d198467 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d198467 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53320 q ha hb
    | true =>
      simp only [d157, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d198467 q = 1) : d200265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d198467 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d198467 q = 1) : d200266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d198467 q = 1) : d200267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d198467 q = 1) : d200268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d198467 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d198467 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53314 q ha hb
    | true =>
      simp only [d204, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d198467 q = 1) : d200272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d198467 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d198467 q = 1) : d200273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d198467 q = 1) : d200274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d200274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d200274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d198467 q = 1) : d200275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d200275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d200275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d198467 q = 1) : d200276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d200276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d200276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro53323 (p : Pattern) (ha : d51652 p = 1) (hb : d198467 p = 1) : d200314 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d198467 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d198467 q = 1) : d200277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d200277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53321 q ha hb
    | true =>
      simp only [d51647, d200277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53322 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d198467 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d198467 q = 1) : d200278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d200278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d200278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d198467 q = 1) : d200279 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d200279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d200279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d198467 q = 1) : d200280 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d200280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d200280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d198467 q = 1) : d200284 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d200284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d200284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53315 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d198467 q = 1) : d200285 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d200285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d200285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d198467 q = 1) : d200286 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d200286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d200286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d198467 q = 1) : d200287 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d200287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d200287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d198467 q = 1) : d200288 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d200288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d200288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d198467 q = 1) : d200309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d200309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d200309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53319 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d198467 q = 1) : d200310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d200310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d200310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d198467 q = 1) : d200311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d200311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d200311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d198467 q = 1) : d200312 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d200312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d200312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d198467 q = 1) : d200313 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d200313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d200313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d198467 q = 1) : d200314 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d200314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d200314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro53324 (p : Pattern) (ha : d284 p = 1) (hb : d198467 p = 1) : d200324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53320 q ha hb
    | true =>
      simp only [d157, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d198467 q = 1) : d200320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d198467 q = 1) : d200321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d198467 q = 1) : d200322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d198467 q = 1) : d200323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d198467 q = 1) : d200324 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53325 (p : Pattern) (ha : d291 p = 1) (hb : d198467 p = 1) : d200331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53320 q ha hb
    | true =>
      simp only [d157, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d198467 q = 1) : d200320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d198467 q = 1) : d200321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d198467 q = 1) : d200322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d198467 q = 1) : d200323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53314 q ha hb
    | true =>
      simp only [d204, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d198467 q = 1) : d200327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d198467 q = 1) : d200328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d198467 q = 1) : d200329 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d198467 q = 1) : d200330 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d198467 q = 1) : d200331 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro53326 (p : Pattern) (ha : d397 p = 1) (hb : d198467 p = 1) : d200404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53320 q ha hb
    | true =>
      simp only [d157, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d198467 q = 1) : d200320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d198467 q = 1) : d200321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d198467 q = 1) : d200322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d198467 q = 1) : d200323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d198467 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d198467 q = 1) : d200404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d200404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d200404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53327 (p : Pattern) (ha : d296 p = 1) (hb : d198467 p = 1) : d200336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53313 q ha hb
    | true =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d198467 q = 1) : d200335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d198467 q = 1) : d200336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d200336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d200336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53328 (p : Pattern) (ha : d303 p = 1) (hb : d198467 p = 1) : d200343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53313 q ha hb
    | true =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d198467 q = 1) : d200341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d198467 q = 1) : d200342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d198467 q = 1) : d200343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d200343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d200343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53329 (p : Pattern) (ha : d4736 p = 1) (hb : d198467 p = 1) : d200377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53313 q ha hb
    | true =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d198467 q = 1) : d200374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d198467 q = 1) : d200375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d198467 q = 1) : d200376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d198467 q = 1) : d200377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d200377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d200377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53330 (p : Pattern) (ha : d318 p = 1) (hb : d198467 p = 1) : d200347 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d316 q = 1) (hb : d152852 q = 1) : d25211 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d25211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316, d25211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d317 q = 1) (hb : d152852 q = 1) : d25212 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d25212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d317, d25212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d318 q = 1) (hb : d198467 q = 1) : d200347 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d198467, d200347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d318, d198467, d200347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53331 (p : Pattern) (ha : d9381 p = 1) (hb : d198467 p = 1) : d200353 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5448 q = 1) (hb : d152852 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5448, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5449 q = 1) (hb : d152852 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5449, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9381 q = 1) (hb : d198467 q = 1) : d200353 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d198467, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9381, d198467, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro53332 (p : Pattern) (ha : d15966 p = 1) (hb : d198467 p = 1) : d200359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53330 q ha hb
    | true =>
      simp only [d319, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53311 q ha hb
    | true =>
      simp only [d139, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d198467 q = 1) : d200352 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53331 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d198467 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d198467 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d198467 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12495 q = 1) (hb : d198467 q = 1) : d200358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12495, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15966 q = 1) (hb : d198467 q = 1) : d200359 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d200359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15966, d200359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro53333 (p : Pattern) (ha : d15972 p = 1) (hb : d198467 p = 1) : d200365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d198467 q = 1) : d200360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53332 q ha hb
    | true =>
      simp only [d15967, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53312 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d198467 q = 1) : d200361 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d198467 q = 1) : d200362 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53312 q ha hb
    | true =>
      simp only [d145, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d198467 q = 1) : d200363 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d198467 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d198467 q = 1) : d200255 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15971 q = 1) (hb : d198467 q = 1) : d200364 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d200364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15971, d200364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15972 q = 1) (hb : d198467 q = 1) : d200365 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d200365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15972, d200365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro53334 (p : Pattern) (ha : d15978 p = 1) (hb : d198467 p = 1) : d200371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d198467 q = 1) : d200366 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53333 q ha hb
    | true =>
      simp only [d15973, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d198467 q = 1) : d200367 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53313 q ha hb
    | true =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d198467 q = 1) : d200368 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d198467 q = 1) : d200369 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d198467 q = 1) : d200370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d198467 q = 1) : d200371 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d200371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d200371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53335 (p : Pattern) (ha : d128195 p = 1) (hb : d198467 p = 1) : d200383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d198467 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d198467 q = 1) : d200337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53327 q ha hb
    | true =>
      simp only [d297, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d198467 q = 1) : d200338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d198467 q = 1) : d200339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d198467 q = 1) : d200340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d198467 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d198467 q = 1) : d200344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53328 q ha hb
    | true =>
      simp only [d304, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d198467 q = 1) : d200345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d198467 q = 1) : d200346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d198467 q = 1) : d200372 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53334 q ha hb
    | true =>
      simp only [d15979, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53320 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d198467 q = 1) : d200373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d198467 q = 1) : d200378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53329 q ha hb
    | true =>
      simp only [d4737, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d198467 q = 1) : d200379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d198467 q = 1) : d200380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d198467 q = 1) : d200381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d198467 q = 1) : d200382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128195 q = 1) (hb : d198467 q = 1) : d200383 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d200383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d200383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro53336 (p : Pattern) (ha : d376 p = 1) (hb : d198467 p = 1) : d200384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53313 q ha hb
    | true =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d198467 q = 1) : d200335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d198467 q = 1) : d200384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d200384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d200384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro53337 (p : Pattern) (ha : d381 p = 1) (hb : d198467 p = 1) : d200389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53313 q ha hb
    | true =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d198467 q = 1) : d200341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d198467 q = 1) : d200342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d198467 q = 1) : d200389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d200389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d200389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro53338 (p : Pattern) (ha : d5355 p = 1) (hb : d198467 p = 1) : d200396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53313 q ha hb
    | true =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d198467 q = 1) : d200374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d198467 q = 1) : d200375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d198467 q = 1) : d200376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d198467 q = 1) : d200396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d200396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d200396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53339 (p : Pattern) (ha : d15985 p = 1) (hb : d198467 p = 1) : d200393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d198467 q = 1) : d200366 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53333 q ha hb
    | true =>
      simp only [d15973, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d198467 q = 1) : d200367 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53313 q ha hb
    | true =>
      simp only [d151, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d198467 q = 1) : d200368 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d198467 q = 1) : d200369 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d198467 q = 1) : d200370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d198467 q = 1) : d200393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d200393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d200393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53340 (p : Pattern) (ha : d128200 p = 1) (hb : d198467 p = 1) : d200402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d198467 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d198467 q = 1) : d200337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53327 q ha hb
    | true =>
      simp only [d297, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d198467 q = 1) : d200338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d198467 q = 1) : d200339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d198467 q = 1) : d200340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d198467 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d198467 q = 1) : d200344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53328 q ha hb
    | true =>
      simp only [d304, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d198467 q = 1) : d200345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d198467 q = 1) : d200346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d198467 q = 1) : d200372 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53334 q ha hb
    | true =>
      simp only [d15979, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53320 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d198467 q = 1) : d200373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d198467 q = 1) : d200378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53329 q ha hb
    | true =>
      simp only [d4737, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d198467 q = 1) : d200379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d198467 q = 1) : d200380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d198467 q = 1) : d200381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d198467 q = 1) : d200382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d198467 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d198467 q = 1) : d200385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d200385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53336 q ha hb
    | true =>
      simp only [d377, d200385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d198467 q = 1) : d200386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d200386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d200386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d198467 q = 1) : d200387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d200387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d200387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d198467 q = 1) : d200388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d200388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d200388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d198467 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d198467 q = 1) : d200390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d200390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53337 q ha hb
    | true =>
      simp only [d382, d200390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d198467 q = 1) : d200391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d200391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d200391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d198467 q = 1) : d200392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d200392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d200392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d15986 q = 1) (hb : d198467 q = 1) : d200394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53339 q ha hb
    | true =>
      simp only [d15986, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53314 q ha hb
  have h27 (q : Pattern) (ha : d128196 q = 1) (hb : d198467 q = 1) : d200395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d128196, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d198467 q = 1) : d200397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53338 q ha hb
    | true =>
      simp only [d5356, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d198467 q = 1) : d200398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d128197 q = 1) (hb : d198467 q = 1) : d200399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d128197, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d128198 q = 1) (hb : d198467 q = 1) : d200400 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d200400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d128198, d200400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d128199 q = 1) (hb : d198467 q = 1) : d200401 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d200401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128199, d200401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d128200 q = 1) (hb : d198467 q = 1) : d200402 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d200402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128200, d200402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro53341 (p : Pattern) (ha : d128207 p = 1) (hb : d198467 p = 1) : d200411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d198467 q = 1) : d200394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53339 q ha hb
    | true =>
      simp only [d15986, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53314 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d198467 q = 1) : d200395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d198467 q = 1) : d200397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53338 q ha hb
    | true =>
      simp only [d5356, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d198467 q = 1) : d200398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d198467 q = 1) : d200399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d198467 q = 1) : d200409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d200409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d200409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d198467 q = 1) : d200410 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d200410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d200410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d198467 q = 1) : d200411 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d200411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d200411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53342 (p : Pattern) (ha : d5377 p = 1) (hb : d198467 p = 1) : d200445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d198467 q = 1) : d200297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53317 q ha hb
    | true =>
      simp only [d238, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d198467 q = 1) : d200298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d198467 q = 1) : d200442 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d200442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d200442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d198467 q = 1) : d200443 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d200443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d200443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d198467 q = 1) : d200444 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d200444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d200444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d198467 q = 1) : d200445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d200445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d200445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53343 (p : Pattern) (ha : d16004 p = 1) (hb : d198467 p = 1) : d200427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d198467 q = 1) : d200417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53330 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53330 q ha hb
    | true =>
      simp only [d319, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d198467 q = 1) : d200418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d198467 q = 1) : d200419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d198467 q = 1) : d200420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53311 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53311 q ha hb
    | true =>
      simp only [d139, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d198467 q = 1) : d200421 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d198467 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53331 q ha hb
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53331 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12600 q = 1) (hb : d198467 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9384 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12601 q = 1) (hb : d198467 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12602 q = 1) (hb : d198467 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d198467 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d12603 q = 1) (hb : d198467 q = 1) : d200426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12603, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d16004 q = 1) (hb : d198467 q = 1) : d200427 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d200427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16004, d200427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro53344 (p : Pattern) (ha : d16010 p = 1) (hb : d198467 p = 1) : d200433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d198467 q = 1) : d200428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53343 q ha hb
    | true =>
      simp only [d16005, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53316 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d198467 q = 1) : d200429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d198467 q = 1) : d200430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53316 q ha hb
    | true =>
      simp only [d232, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d198467 q = 1) : d200431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d198467 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d198467 q = 1) : d200294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16009 q = 1) (hb : d198467 q = 1) : d200432 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d200432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, d200432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16010 q = 1) (hb : d198467 q = 1) : d200433 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d200433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16010, d200433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro53345 (p : Pattern) (ha : d16016 p = 1) (hb : d198467 p = 1) : d200439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d198467 q = 1) : d200434 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d200434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53344 q ha hb
    | true =>
      simp only [d16011, d200434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d198467 q = 1) : d200435 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d200435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d200435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d198467 q = 1) : d200297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53317 q ha hb
    | true =>
      simp only [d238, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d198467 q = 1) : d200298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d198467 q = 1) : d200436 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d200436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d200436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d198467 q = 1) : d200437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d200437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d200437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d198467 q = 1) : d200438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d200438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d200438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d198467 q = 1) : d200439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d200439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d200439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53346 (p : Pattern) (ha : d128217 p = 1) (hb : d198467 p = 1) : d200451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d198467 q = 1) : d200440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d200440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53345 q ha hb
    | true =>
      simp only [d16017, d200440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53318 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d198467 q = 1) : d200441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d200441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d200441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d198467 q = 1) : d200446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d200446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53342 q ha hb
    | true =>
      simp only [d5378, d200446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d198467 q = 1) : d200447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d200447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d200447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d198467 q = 1) : d200448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d200448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d200448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d198467 q = 1) : d200449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d200449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d200449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d198467 q = 1) : d200450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d200450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d200450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d198467 q = 1) : d200451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d200451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d200451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53347 (p : Pattern) (ha : d128223 p = 1) (hb : d198467 p = 1) : d200457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d198467 q = 1) : d200325 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d200325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d200325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53324 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d198467 q = 1) : d200326 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d200326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d200326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d198467 q = 1) : d200332 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53324 q ha hb
    | true =>
      simp only [d292, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53325 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d198467 q = 1) : d200333 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d198467 q = 1) : d200334 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d200334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d200334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d198467 q = 1) : d200403 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d200403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53335 q ha hb
    | true =>
      simp only [d128201, d200403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53340 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d198467 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d198467 q = 1) : d200405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d200405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53326 q ha hb
    | true =>
      simp only [d398, d200405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128202 q = 1) (hb : d198467 q = 1) : d200406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d200406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d200406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128203 q = 1) (hb : d198467 q = 1) : d200407 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d200407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128203, d200407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d128204 q = 1) (hb : d198467 q = 1) : d200408 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d200408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, d200408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128208 q = 1) (hb : d198467 q = 1) : d200412 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d200412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, d200412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53341 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d198467 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d128209 q = 1) (hb : d198467 q = 1) : d200413 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d200413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128209, d200413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128210 q = 1) (hb : d198467 q = 1) : d200414 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d200414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128210, d200414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128211 q = 1) (hb : d198467 q = 1) : d200415 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d200415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128211, d200415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d128212 q = 1) (hb : d198467 q = 1) : d200416 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d200416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128212, d200416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128218 q = 1) (hb : d198467 q = 1) : d200452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d200452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, d200452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53346 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d198467 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d128219 q = 1) (hb : d198467 q = 1) : d200453 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d200453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128219, d200453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d128220 q = 1) (hb : d198467 q = 1) : d200454 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d200454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128220, d200454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128221 q = 1) (hb : d198467 q = 1) : d200455 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d200455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128221, d200455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128222 q = 1) (hb : d198467 q = 1) : d200456 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d200456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128222, d200456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d128223 q = 1) (hb : d198467 q = 1) : d200457 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d200457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128223, d200457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro53348 (p : Pattern) (ha : d128229 p = 1) (hb : d198467 p = 1) : d200463 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d198467 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d198467 q = 1) : d200315 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d200315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d200315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53323 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d198467 q = 1) : d200316 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d200316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d200316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d198467 q = 1) : d200317 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d200317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d200317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d198467 q = 1) : d200318 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d200318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d200318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d198467 q = 1) : d200319 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d200319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d200319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d198467 q = 1) : d200458 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d200458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d200458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53347 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d198467 q = 1) : d200459 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d200459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d200459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d198467 q = 1) : d200460 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d200460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d200460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d198467 q = 1) : d200461 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d200461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d200461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d198467 q = 1) : d200462 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d200462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d200462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d198467 q = 1) : d200463 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d200463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d200463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro53349 (p : Pattern) (ha : d481 p = 1) (hb : d198467 p = 1) : d200470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53312 q ha hb
    | true =>
      simp only [d145, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d198467 q = 1) : d200464 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d198467 q = 1) : d200469 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d200469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d200469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d198467 q = 1) : d200470 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d200470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d200470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro53350 (p : Pattern) (ha : d491 p = 1) (hb : d198467 p = 1) : d200480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d198467 q = 1) : d200479 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d198467 q = 1) : d200480 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d200480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d200480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53351 (p : Pattern) (ha : d501 p = 1) (hb : d198467 p = 1) : d200490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d198467 q = 1) : d200479 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d198467 q = 1) : d200490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d200490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d200490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53352 (p : Pattern) (ha : d644 p = 1) (hb : d198467 p = 1) : d200591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d198467 q = 1) : d200580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53350 q ha hb
    | true =>
      simp only [d633, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d198467 q = 1) : d200581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d198467 q = 1) : d200582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d198467 q = 1) : d200583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d198467 q = 1) : d200584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d198467 q = 1) : d200586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53351 q ha hb
    | true =>
      simp only [d639, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d198467 q = 1) : d200587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d198467 q = 1) : d200588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d198467 q = 1) : d200589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d198467 q = 1) : d200590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d198467 q = 1) : d200591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d200591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d200591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53353 (p : Pattern) (ha : d653 p = 1) (hb : d198467 p = 1) : d200600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d198467 q = 1) : d200586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53351 q ha hb
    | true =>
      simp only [d639, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d198467 q = 1) : d200587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d198467 q = 1) : d200588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d198467 q = 1) : d200589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d198467 q = 1) : d200590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d198467 q = 1) : d200600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d200600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d200600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53354 (p : Pattern) (ha : d683 p = 1) (hb : d198467 p = 1) : d200639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53316 q ha hb
    | true =>
      simp only [d232, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d198467 q = 1) : d200629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d198467 q = 1) : d200638 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d200638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d200638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d198467 q = 1) : d200639 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d200639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d200639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro53355 (p : Pattern) (ha : d730 p = 1) (hb : d198467 p = 1) : d200662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d198467 q = 1) : d200640 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53354 q ha hb
    | true =>
      simp only [d684, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d198467 q = 1) : d200641 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d198467 q = 1) : d200659 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d200659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d200659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d198467 q = 1) : d200660 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d200660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d200660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d198467 q = 1) : d200661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d200661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d200661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d198467 q = 1) : d200662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d200662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d200662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53356 (p : Pattern) (ha : d736 p = 1) (hb : d198467 p = 1) : d200668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d198467 q = 1) : d200663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d200663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53355 q ha hb
    | true =>
      simp only [d731, d200663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d198467 q = 1) : d200664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d200664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d200664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d198467 q = 1) : d200665 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d200665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d200665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d198467 q = 1) : d200666 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d200666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d200666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d198467 q = 1) : d200667 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d200667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d200667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d198467 q = 1) : d200668 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d200668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d200668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53357 (p : Pattern) (ha : d16036 p = 1) (hb : d198467 p = 1) : d200466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d198467 q = 1) : d200360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53332 q ha hb
    | true =>
      simp only [d15967, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53312 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d198467 q = 1) : d200361 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d198467 q = 1) : d200362 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53312 q ha hb
    | true =>
      simp only [d145, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d198467 q = 1) : d200363 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d198467 q = 1) : d200464 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16035 q = 1) (hb : d198467 q = 1) : d200465 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d200465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16035, d200465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16036 q = 1) (hb : d198467 q = 1) : d200466 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d200466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16036, d200466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro53358 (p : Pattern) (ha : d16042 p = 1) (hb : d198467 p = 1) : d200476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53357 q ha hb
    | true =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d198467 q = 1) : d200475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d198467 q = 1) : d200476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d200476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d200476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53359 (p : Pattern) (ha : d16048 p = 1) (hb : d198467 p = 1) : d200486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d198467 q = 1) : d200481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53358 q ha hb
    | true =>
      simp only [d16043, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53350 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d198467 q = 1) : d200482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d198467 q = 1) : d200483 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d198467 q = 1) : d200484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d198467 q = 1) : d200485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d198467 q = 1) : d200486 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53360 (p : Pattern) (ha : d16051 p = 1) (hb : d198467 p = 1) : d200489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53357 q ha hb
    | true =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d198467 q = 1) : d200475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d198467 q = 1) : d200489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d200489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d200489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53361 (p : Pattern) (ha : d16057 p = 1) (hb : d198467 p = 1) : d200496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d198467 q = 1) : d200481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53358 q ha hb
    | true =>
      simp only [d16043, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53350 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d198467 q = 1) : d200482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d198467 q = 1) : d200483 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d198467 q = 1) : d200484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d198467 q = 1) : d200485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d198467 q = 1) : d200491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53360 q ha hb
    | true =>
      simp only [d16052, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53351 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d198467 q = 1) : d200492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d198467 q = 1) : d200493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d198467 q = 1) : d200494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d198467 q = 1) : d200495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d198467 q = 1) : d200496 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53362 (p : Pattern) (ha : d16143 p = 1) (hb : d198467 p = 1) : d200585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d198467 q = 1) : d200481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53358 q ha hb
    | true =>
      simp only [d16043, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53350 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d198467 q = 1) : d200482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d198467 q = 1) : d200483 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d198467 q = 1) : d200484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d198467 q = 1) : d200485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d198467 q = 1) : d200580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53350 q ha hb
    | true =>
      simp only [d633, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d198467 q = 1) : d200581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d198467 q = 1) : d200582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d198467 q = 1) : d200583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d198467 q = 1) : d200584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d198467 q = 1) : d200585 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d200585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d200585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53363 (p : Pattern) (ha : d514 p = 1) (hb : d198467 p = 1) : d200503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d198467 q = 1) : d200502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d198467 q = 1) : d200503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d200503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d200503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53364 (p : Pattern) (ha : d524 p = 1) (hb : d198467 p = 1) : d200513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d198467 q = 1) : d200511 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d198467 q = 1) : d200512 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d198467 q = 1) : d200513 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d200513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d200513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53365 (p : Pattern) (ha : d16062 p = 1) (hb : d198467 p = 1) : d200501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53357 q ha hb
    | true =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d198467 q = 1) : d200500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d198467 q = 1) : d200501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d200501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d200501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53366 (p : Pattern) (ha : d16069 p = 1) (hb : d198467 p = 1) : d200510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53357 q ha hb
    | true =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d198467 q = 1) : d200508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d198467 q = 1) : d200509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d198467 q = 1) : d200510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d200510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d200510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53367 (p : Pattern) (ha : d542 p = 1) (hb : d198467 p = 1) : d200517 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d538 q = 1) : d538 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d539 q = 1) (hb : d152852 q = 1) : d25429 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d540 q = 1) (hb : d152852 q = 1) : d25430 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d25430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d540, d25430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d541 q = 1) (hb : d152852 q = 1) : d25431 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d25431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d541, d25431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d317 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d542 q = 1) (hb : d198467 q = 1) : d200517 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d542, d198467, d200517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d542, d198467, d200517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53368 (p : Pattern) (ha : d9457 p = 1) (hb : d198467 p = 1) : d200347 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d316 q = 1) (hb : d152852 q = 1) : d25211 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d25211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316, d25211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d317 q = 1) (hb : d152852 q = 1) : d25212 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d25212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d317, d25212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9456 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9457 q = 1) (hb : d198467 q = 1) : d200347 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9457, d198467, d200347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9457, d198467, d200347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53369 (p : Pattern) (ha : d9467 p = 1) (hb : d198467 p = 1) : d200523 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d314 q = 1) : d314 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9464 q = 1) (hb : d152852 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9464, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9464, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9465 q = 1) (hb : d152852 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9465, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9465, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9466 q = 1) (hb : d152852 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9466, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9466, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9456 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9467 q = 1) (hb : d198467 q = 1) : d200523 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9467, d198467, d200523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9467, d198467, d200523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro53370 (p : Pattern) (ha : d16077 p = 1) (hb : d198467 p = 1) : d200529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53367 q ha hb
    | true =>
      simp only [d543, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d198467 q = 1) : d200520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d198467 q = 1) : d200521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9458 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53368 q ha hb
    | true =>
      simp only [d9458, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9460, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16073 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16074 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16074, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16075 q = 1) (hb : d198467 q = 1) : d200522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9468 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
    | true =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12748 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12749 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12749, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9382 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53331 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9384 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12493 q = 1) (hb : d198467 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12494 q = 1) (hb : d198467 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16076 q = 1) (hb : d198467 q = 1) : d200528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16076, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16076, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16077 q = 1) (hb : d198467 q = 1) : d200529 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16077, d200529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16077, d200529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro53371 (p : Pattern) (ha : d16081 p = 1) (hb : d198467 p = 1) : d200533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53331 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d198467 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d198467 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d198467 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12495 q = 1) (hb : d198467 q = 1) : d200358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d198467 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16081 q = 1) (hb : d198467 q = 1) : d200533 q = 1 := by
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
theorem andIntro53372 (p : Pattern) (ha : d16087 p = 1) (hb : d198467 p = 1) : d200539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16078 q = 1) (hb : d198467 q = 1) : d200530 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d200530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53370 q ha hb
    | true =>
      simp only [d16078, d200530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53332 q ha hb
  have h2 (q : Pattern) (ha : d16079 q = 1) (hb : d198467 q = 1) : d200531 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16079, d200531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16079, d200531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16080 q = 1) (hb : d198467 q = 1) : d200532 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16080, d200532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16080, d200532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d198467 q = 1) : d200534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d200534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53332 q ha hb
    | true =>
      simp only [d16082, d200534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53371 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d198467 q = 1) : d200535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d200535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d200535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d198467 q = 1) : d200536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d200536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d200536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16085 q = 1) (hb : d198467 q = 1) : d200537 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16085, d200537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16085, d200537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d198467 q = 1) : d200360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53332 q ha hb
    | true =>
      simp only [d15967, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53312 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d198467 q = 1) : d200361 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d198467 q = 1) : d200362 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d145 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53312 q ha hb
    | true =>
      simp only [d145, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15970 q = 1) (hb : d198467 q = 1) : d200363 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16086 q = 1) (hb : d198467 q = 1) : d200538 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16086, d200538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16086, d200538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16087 q = 1) (hb : d198467 q = 1) : d200539 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16087, d200539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16087, d200539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro53373 (p : Pattern) (ha : d16093 p = 1) (hb : d198467 p = 1) : d200545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d198467 q = 1) : d200540 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53372 q ha hb
    | true =>
      simp only [d16088, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d198467 q = 1) : d200541 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53357 q ha hb
    | true =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d198467 q = 1) : d200542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d198467 q = 1) : d200543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d198467 q = 1) : d200544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16093 q = 1) (hb : d198467 q = 1) : d200545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16093, d200545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16093, d200545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53374 (p : Pattern) (ha : d16114 p = 1) (hb : d198467 p = 1) : d200551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53357 q ha hb
    | true =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d198467 q = 1) : d200548 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d198467 q = 1) : d200549 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d198467 q = 1) : d200550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d198467 q = 1) : d200551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d200551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d200551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53375 (p : Pattern) (ha : d128234 p = 1) (hb : d198467 p = 1) : d200557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d198467 q = 1) : d200504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53365 q ha hb
    | true =>
      simp only [d16063, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53363 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d198467 q = 1) : d200505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d198467 q = 1) : d200506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d198467 q = 1) : d200507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d198467 q = 1) : d200514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53366 q ha hb
    | true =>
      simp only [d16070, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53364 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d198467 q = 1) : d200515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d198467 q = 1) : d200516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d198467 q = 1) : d200546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53373 q ha hb
    | true =>
      simp only [d16094, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53358 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d198467 q = 1) : d200547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d198467 q = 1) : d200552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53374 q ha hb
    | true =>
      simp only [d16115, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d198467 q = 1) : d200553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d198467 q = 1) : d200554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d198467 q = 1) : d200555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d198467 q = 1) : d200556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128234 q = 1) (hb : d198467 q = 1) : d200557 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128234, d200557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128234, d200557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53376 (p : Pattern) (ha : d610 p = 1) (hb : d198467 p = 1) : d200559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d198467 q = 1) : d200502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d198467 q = 1) : d200559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d200559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d200559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53377 (p : Pattern) (ha : d616 p = 1) (hb : d198467 p = 1) : d200565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d198467 q = 1) : d200511 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d198467 q = 1) : d200512 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d198467 q = 1) : d200565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d200565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d200565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53378 (p : Pattern) (ha : d16121 p = 1) (hb : d198467 p = 1) : d200558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53357 q ha hb
    | true =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d198467 q = 1) : d200500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d198467 q = 1) : d200558 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d200558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d200558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53379 (p : Pattern) (ha : d16126 p = 1) (hb : d198467 p = 1) : d200564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53357 q ha hb
    | true =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53349 q ha hb
    | true =>
      simp only [d482, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d198467 q = 1) : d200508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d198467 q = 1) : d200509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d198467 q = 1) : d200564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d200564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d200564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53380 (p : Pattern) (ha : d16130 p = 1) (hb : d198467 p = 1) : d200569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d198467 q = 1) : d200540 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53372 q ha hb
    | true =>
      simp only [d16088, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d198467 q = 1) : d200541 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53357 q ha hb
    | true =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d198467 q = 1) : d200542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d198467 q = 1) : d200543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d198467 q = 1) : d200544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16130 q = 1) (hb : d198467 q = 1) : d200569 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16130, d200569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16130, d200569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53381 (p : Pattern) (ha : d16135 p = 1) (hb : d198467 p = 1) : d200572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53357 q ha hb
    | true =>
      simp only [d16037, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d198467 q = 1) : d200548 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d198467 q = 1) : d200549 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d198467 q = 1) : d200550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d198467 q = 1) : d200572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d200572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d200572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53382 (p : Pattern) (ha : d128239 p = 1) (hb : d198467 p = 1) : d200578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d198467 q = 1) : d200504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53365 q ha hb
    | true =>
      simp only [d16063, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53363 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d198467 q = 1) : d200505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d198467 q = 1) : d200506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d198467 q = 1) : d200507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d198467 q = 1) : d200514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53366 q ha hb
    | true =>
      simp only [d16070, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53364 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d198467 q = 1) : d200515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d198467 q = 1) : d200516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d198467 q = 1) : d200546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53373 q ha hb
    | true =>
      simp only [d16094, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53358 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d198467 q = 1) : d200547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d198467 q = 1) : d200552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53374 q ha hb
    | true =>
      simp only [d16115, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d198467 q = 1) : d200553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d198467 q = 1) : d200554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d198467 q = 1) : d200555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d198467 q = 1) : d200556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d198467 q = 1) : d200560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d200560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53378 q ha hb
    | true =>
      simp only [d16122, d200560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53376 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d198467 q = 1) : d200561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d200561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d200561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d198467 q = 1) : d200562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d200562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d200562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d198467 q = 1) : d200563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d200563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d200563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d198467 q = 1) : d200566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d200566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53379 q ha hb
    | true =>
      simp only [d16127, d200566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53377 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d198467 q = 1) : d200567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d200567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d200567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d198467 q = 1) : d200568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d200568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d200568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16131 q = 1) (hb : d198467 q = 1) : d200570 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53380 q ha hb
    | true =>
      simp only [d16131, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53360 q ha hb
  have h23 (q : Pattern) (ha : d128235 q = 1) (hb : d198467 q = 1) : d200571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128235, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d198467 q = 1) : d200573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53381 q ha hb
    | true =>
      simp only [d16136, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d198467 q = 1) : d200574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128236 q = 1) (hb : d198467 q = 1) : d200575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128236, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128237 q = 1) (hb : d198467 q = 1) : d200576 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128237, d200576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128237, d200576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128238 q = 1) (hb : d198467 q = 1) : d200577 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128238, d200577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128238, d200577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128239 q = 1) (hb : d198467 q = 1) : d200578 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128239, d200578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128239, d200578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro53383 (p : Pattern) (ha : d128246 p = 1) (hb : d198467 p = 1) : d200598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16131 q = 1) (hb : d198467 q = 1) : d200570 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53380 q ha hb
    | true =>
      simp only [d16131, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53360 q ha hb
  have h2 (q : Pattern) (ha : d128235 q = 1) (hb : d198467 q = 1) : d200571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128235, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d198467 q = 1) : d200573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53381 q ha hb
    | true =>
      simp only [d16136, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d198467 q = 1) : d200574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128236 q = 1) (hb : d198467 q = 1) : d200575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128236, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128244 q = 1) (hb : d198467 q = 1) : d200596 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128244, d200596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128244, d200596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128245 q = 1) (hb : d198467 q = 1) : d200597 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128245, d200597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128245, d200597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128246 q = 1) (hb : d198467 q = 1) : d200598 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d200598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d200598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53384 (p : Pattern) (ha : d16162 p = 1) (hb : d198467 p = 1) : d200616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d198467 q = 1) : d200606 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53367 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53367 q ha hb
    | true =>
      simp only [d543, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d198467 q = 1) : d200607 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d198467 q = 1) : d200608 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d198467 q = 1) : d200609 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16156 q = 1) (hb : d198467 q = 1) : d200417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53368 q ha hb
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53368 q ha hb
    | true =>
      simp only [d9458, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d198467 q = 1) : d200418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16157, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9460 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9460, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16158 q = 1) (hb : d198467 q = 1) : d200419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16158, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16159 q = 1) (hb : d198467 q = 1) : d200420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16159, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16160 q = 1) (hb : d198467 q = 1) : d200610 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d200610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16160, d200610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12858 q = 1) (hb : d198467 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
  have h15 (q : Pattern) (ha : d9468 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
    | true =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12859 q = 1) (hb : d198467 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12859, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9470 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12860 q = 1) (hb : d198467 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12860, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12861 q = 1) (hb : d198467 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12861, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12599 q = 1) (hb : d198467 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53331 q ha hb
  have h21 (q : Pattern) (ha : d9382 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53331 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12600 q = 1) (hb : d198467 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9384 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12601 q = 1) (hb : d198467 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12602 q = 1) (hb : d198467 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16161 q = 1) (hb : d198467 q = 1) : d200615 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16161, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16161, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16162 q = 1) (hb : d198467 q = 1) : d200616 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16162, d200616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16162, d200616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro53385 (p : Pattern) (ha : d16166 p = 1) (hb : d198467 p = 1) : d200620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d198467 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53331 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53331 q ha hb
    | true =>
      simp only [d9382, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d198467 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d198467 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d198467 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d198467 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12603 q = 1) (hb : d198467 q = 1) : d200426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d198467 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16166 q = 1) (hb : d198467 q = 1) : d200620 q = 1 := by
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
theorem andIntro53386 (p : Pattern) (ha : d16172 p = 1) (hb : d198467 p = 1) : d200626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16163 q = 1) (hb : d198467 q = 1) : d200617 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d200617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53384 q ha hb
    | true =>
      simp only [d16163, d200617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53343 q ha hb
  have h2 (q : Pattern) (ha : d16164 q = 1) (hb : d198467 q = 1) : d200618 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d200618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16164, d200618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16165 q = 1) (hb : d198467 q = 1) : d200619 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d200619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, d200619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d198467 q = 1) : d200621 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d200621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53343 q ha hb
    | true =>
      simp only [d16167, d200621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53385 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d198467 q = 1) : d200622 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d200622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d200622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d198467 q = 1) : d200623 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d200623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d200623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16170 q = 1) (hb : d198467 q = 1) : d200624 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d200624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16170, d200624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d198467 q = 1) : d200428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53343 q ha hb
    | true =>
      simp only [d16005, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53316 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d198467 q = 1) : d200429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d198467 q = 1) : d200430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d232 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53316 q ha hb
    | true =>
      simp only [d232, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16008 q = 1) (hb : d198467 q = 1) : d200431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16171 q = 1) (hb : d198467 q = 1) : d200625 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d200625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16171, d200625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16172 q = 1) (hb : d198467 q = 1) : d200626 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16172, d200626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16172, d200626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro53387 (p : Pattern) (ha : d16176 p = 1) (hb : d198467 p = 1) : d200631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d198467 q = 1) : d200428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53343 q ha hb
    | true =>
      simp only [d16005, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53316 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d198467 q = 1) : d200429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d198467 q = 1) : d200430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53316 q ha hb
    | true =>
      simp only [d232, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d198467 q = 1) : d200431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d198467 q = 1) : d200629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d198467 q = 1) : d200630 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d200630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, d200630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16176 q = 1) (hb : d198467 q = 1) : d200631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d200631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16176, d200631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro53388 (p : Pattern) (ha : d16182 p = 1) (hb : d198467 p = 1) : d200637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16173 q = 1) (hb : d198467 q = 1) : d200627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16173, d200627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53386 q ha hb
    | true =>
      simp only [d16173, d200627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16174 q = 1) (hb : d198467 q = 1) : d200628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16174, d200628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16174, d200628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d198467 q = 1) : d200632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53387 q ha hb
    | true =>
      simp only [d16177, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d198467 q = 1) : d200633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16179 q = 1) (hb : d198467 q = 1) : d200634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16179, d200634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16179, d200634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16180 q = 1) (hb : d198467 q = 1) : d200635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16180, d200635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16180, d200635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16181 q = 1) (hb : d198467 q = 1) : d200636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16181, d200636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16181, d200636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16182 q = 1) (hb : d198467 q = 1) : d200637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16182, d200637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16182, d200637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53389 (p : Pattern) (ha : d16186 p = 1) (hb : d198467 p = 1) : d200645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d198467 q = 1) : d200632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53387 q ha hb
    | true =>
      simp only [d16177, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d198467 q = 1) : d200633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d198467 q = 1) : d200640 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53354 q ha hb
    | true =>
      simp only [d684, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d198467 q = 1) : d200641 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d198467 q = 1) : d200642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d200642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d200642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d198467 q = 1) : d200643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d200643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d200643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d198467 q = 1) : d200644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d200644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d200644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d198467 q = 1) : d200645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d200645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d200645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53390 (p : Pattern) (ha : d16207 p = 1) (hb : d198467 p = 1) : d200651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d198467 q = 1) : d200632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53387 q ha hb
    | true =>
      simp only [d16177, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d198467 q = 1) : d200633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d198467 q = 1) : d200648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d200648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d200648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d198467 q = 1) : d200649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d200649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d200649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d198467 q = 1) : d200650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d200650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d200650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d198467 q = 1) : d200651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d200651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d200651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53391 (p : Pattern) (ha : d128256 p = 1) (hb : d198467 p = 1) : d200657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16187 q = 1) (hb : d198467 q = 1) : d200646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16187, d200646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53388 q ha hb
    | true =>
      simp only [d16187, d200646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53389 q ha hb
  have h2 (q : Pattern) (ha : d128252 q = 1) (hb : d198467 q = 1) : d200647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d200647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128252, d200647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d198467 q = 1) : d200652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d200652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53390 q ha hb
    | true =>
      simp only [d16208, d200652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d198467 q = 1) : d200653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d200653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d200653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d198467 q = 1) : d200654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d200654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128253, d200654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d198467 q = 1) : d200655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d200655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d200655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d198467 q = 1) : d200656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d200656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d200656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d198467 q = 1) : d200657 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d200657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d200657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53392 (p : Pattern) (ha : d128262 p = 1) (hb : d198467 p = 1) : d200674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d198467 q = 1) : d200487 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d200487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d200487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53359 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d198467 q = 1) : d200488 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d200488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d200488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d198467 q = 1) : d200497 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53359 q ha hb
    | true =>
      simp only [d16058, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53361 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d198467 q = 1) : d200498 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d198467 q = 1) : d200499 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d200499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d200499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128240 q = 1) (hb : d198467 q = 1) : d200579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128240, d200579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53375 q ha hb
    | true =>
      simp only [d128240, d200579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53382 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d198467 q = 1) : d200592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d200592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53362 q ha hb
    | true =>
      simp only [d16144, d200592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53352 q ha hb
  have h8 (q : Pattern) (ha : d128241 q = 1) (hb : d198467 q = 1) : d200593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128241, d200593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128241, d200593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128242 q = 1) (hb : d198467 q = 1) : d200594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d200594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128242, d200594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128243 q = 1) (hb : d198467 q = 1) : d200595 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d200595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128243, d200595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128247 q = 1) (hb : d198467 q = 1) : d200599 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d200599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128247, d200599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53383 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d198467 q = 1) : d200601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d200601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d200601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53353 q ha hb
  have h13 (q : Pattern) (ha : d128248 q = 1) (hb : d198467 q = 1) : d200602 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d200602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128248, d200602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128249 q = 1) (hb : d198467 q = 1) : d200603 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d200603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128249, d200603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128250 q = 1) (hb : d198467 q = 1) : d200604 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d200604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128250, d200604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128251 q = 1) (hb : d198467 q = 1) : d200605 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d200605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128251, d200605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128257 q = 1) (hb : d198467 q = 1) : d200658 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d200658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128257, d200658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53391 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d198467 q = 1) : d200669 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d200669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d200669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53356 q ha hb
  have h19 (q : Pattern) (ha : d128258 q = 1) (hb : d198467 q = 1) : d200670 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d200670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128258, d200670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128259 q = 1) (hb : d198467 q = 1) : d200671 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d200671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128259, d200671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128260 q = 1) (hb : d198467 q = 1) : d200672 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d200672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128260, d200672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128261 q = 1) (hb : d198467 q = 1) : d200673 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d200673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128261, d200673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128262 q = 1) (hb : d198467 q = 1) : d200674 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d200674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128262, d200674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro53393 (p : Pattern) (ha : d128268 p = 1) (hb : d198467 p = 1) : d200680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d198467 q = 1) : d200675 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d200675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d200675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53392 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d198467 q = 1) : d200676 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d200676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d200676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d198467 q = 1) : d200677 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d200677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d200677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d198467 q = 1) : d200678 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d200678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d200678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d198467 q = 1) : d200679 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d200679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d200679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d198467 q = 1) : d200680 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d200680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d200680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53394 (p : Pattern) (ha : d758 p = 1) (hb : d198467 p = 1) : d200684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53330 q ha hb
    | true =>
      simp only [d319, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d198467 q = 1) : d200352 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d198467 q = 1) : d25698 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d758 q = 1) (hb : d198467 q = 1) : d200684 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d200684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d758, d200684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53395 (p : Pattern) (ha : d773 p = 1) (hb : d198467 p = 1) : d200698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d198467 q = 1) : d200688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53394 q ha hb
    | true =>
      simp only [d763, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47182 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d198467 q = 1) : d200689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d198467 q = 1) : d200690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d767 q = 1) (hb : d198467 q = 1) : d200692 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d772 q = 1) (hb : d198467 q = 1) : d200697 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d200697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d772, d200697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d773 q = 1) (hb : d198467 q = 1) : d200698 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d200698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d773, d200698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53396 (p : Pattern) (ha : d783 p = 1) (hb : d198467 p = 1) : d200708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d198467 q = 1) : d200706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d198467 q = 1) : d200707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d198467 q = 1) : d200708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d200708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d200708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53397 (p : Pattern) (ha : d793 p = 1) (hb : d198467 p = 1) : d200718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d198467 q = 1) : d200706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d198467 q = 1) : d200707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d198467 q = 1) : d200718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d200718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d200718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53398 (p : Pattern) (ha : d950 p = 1) (hb : d198467 p = 1) : d200819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d198467 q = 1) : d200808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53396 q ha hb
    | true =>
      simp only [d939, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d198467 q = 1) : d200809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d198467 q = 1) : d200810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d198467 q = 1) : d200811 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d198467 q = 1) : d200812 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d198467 q = 1) : d200814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53397 q ha hb
    | true =>
      simp only [d945, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d198467 q = 1) : d200815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d198467 q = 1) : d200816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d198467 q = 1) : d200817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d198467 q = 1) : d200818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d198467 q = 1) : d200819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d200819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d200819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53399 (p : Pattern) (ha : d959 p = 1) (hb : d198467 p = 1) : d200828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d198467 q = 1) : d200814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53397 q ha hb
    | true =>
      simp only [d945, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d198467 q = 1) : d200815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d198467 q = 1) : d200816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d198467 q = 1) : d200817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d198467 q = 1) : d200818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d198467 q = 1) : d200828 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d200828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d200828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53400 (p : Pattern) (ha : d981 p = 1) (hb : d198467 p = 1) : d200855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d198467 q = 1) : d200417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53330 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53330 q ha hb
    | true =>
      simp only [d319, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d198467 q = 1) : d200418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d198467 q = 1) : d200419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d198467 q = 1) : d200420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d198467 q = 1) : d200421 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d198467 q = 1) : d25957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d981 q = 1) (hb : d198467 q = 1) : d200855 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d200855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d981, d200855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53401 (p : Pattern) (ha : d1005 p = 1) (hb : d198467 p = 1) : d200877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d198467 q = 1) : d200859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53400 q ha hb
    | true =>
      simp only [d987, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47196 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d198467 q = 1) : d200860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d198467 q = 1) : d200861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d198467 q = 1) : d200867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d200867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d200867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d198467 q = 1) : d200876 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d200876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d200876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1005 q = 1) (hb : d198467 q = 1) : d200877 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d200877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1005, d200877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53402 (p : Pattern) (ha : d1063 p = 1) (hb : d198467 p = 1) : d200900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d198467 q = 1) : d200878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d200878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53401 q ha hb
    | true =>
      simp only [d1006, d200878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d198467 q = 1) : d200879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d200879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d200879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d198467 q = 1) : d200897 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d200897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d200897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d198467 q = 1) : d200898 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d200898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d200898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d198467 q = 1) : d200899 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d200899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d200899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d198467 q = 1) : d200900 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d200900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d200900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53403 (p : Pattern) (ha : d1069 p = 1) (hb : d198467 p = 1) : d200906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d198467 q = 1) : d200901 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d200901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53402 q ha hb
    | true =>
      simp only [d1064, d200901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d198467 q = 1) : d200902 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d200902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d200902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d198467 q = 1) : d200903 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d200903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d200903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d198467 q = 1) : d200904 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d200904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d200904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d198467 q = 1) : d200905 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d200905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d200905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d198467 q = 1) : d200906 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d200906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d200906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53404 (p : Pattern) (ha : d16227 p = 1) (hb : d198467 p = 1) : d200683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53367 q ha hb
    | true =>
      simp only [d543, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d198467 q = 1) : d200520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d198467 q = 1) : d200521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9458 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53368 q ha hb
    | true =>
      simp only [d9458, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9460, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16073 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16074 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16074, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16075 q = 1) (hb : d198467 q = 1) : d200522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9468 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
    | true =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12748 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12749 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12749, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d753 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d754 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12750 q = 1) (hb : d198467 q = 1) : d200682 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12750, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16227 q = 1) (hb : d198467 q = 1) : d200683 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16227, d200683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16227, d200683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro53405 (p : Pattern) (ha : d16233 p = 1) (hb : d198467 p = 1) : d200694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16228 q = 1) (hb : d198467 q = 1) : d200685 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53404 q ha hb
    | true =>
      simp only [d16228, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53394 q ha hb
  have h2 (q : Pattern) (ha : d16229 q = 1) (hb : d198467 q = 1) : d200686 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16230 q = 1) (hb : d198467 q = 1) : d200687 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d198467 q = 1) : d200688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53394 q ha hb
    | true =>
      simp only [d763, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47182 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d198467 q = 1) : d200689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d198467 q = 1) : d200690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16231 q = 1) (hb : d198467 q = 1) : d200691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16231, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d198467 q = 1) : d200692 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16232 q = 1) (hb : d198467 q = 1) : d200693 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16232, d200693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16232, d200693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16233 q = 1) (hb : d198467 q = 1) : d200694 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16233, d200694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16233, d200694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro53406 (p : Pattern) (ha : d16239 p = 1) (hb : d198467 p = 1) : d200704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53405 q ha hb
    | true =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d198467 q = 1) : d200702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d198467 q = 1) : d200703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16239 q = 1) (hb : d198467 q = 1) : d200704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16239, d200704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16239, d200704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53407 (p : Pattern) (ha : d16245 p = 1) (hb : d198467 p = 1) : d200714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d198467 q = 1) : d200709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53406 q ha hb
    | true =>
      simp only [d16240, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53396 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d198467 q = 1) : d200710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d198467 q = 1) : d200711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d198467 q = 1) : d200712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d198467 q = 1) : d200713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16245 q = 1) (hb : d198467 q = 1) : d200714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16245, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16245, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53408 (p : Pattern) (ha : d16248 p = 1) (hb : d198467 p = 1) : d200717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53405 q ha hb
    | true =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d198467 q = 1) : d200702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d198467 q = 1) : d200703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16248 q = 1) (hb : d198467 q = 1) : d200717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16248, d200717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16248, d200717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53409 (p : Pattern) (ha : d16254 p = 1) (hb : d198467 p = 1) : d200724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d198467 q = 1) : d200709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53406 q ha hb
    | true =>
      simp only [d16240, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53396 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d198467 q = 1) : d200710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d198467 q = 1) : d200711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d198467 q = 1) : d200712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d198467 q = 1) : d200713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16249 q = 1) (hb : d198467 q = 1) : d200719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53408 q ha hb
    | true =>
      simp only [d16249, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53397 q ha hb
  have h7 (q : Pattern) (ha : d16250 q = 1) (hb : d198467 q = 1) : d200720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16251 q = 1) (hb : d198467 q = 1) : d200721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16251, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16252 q = 1) (hb : d198467 q = 1) : d200722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16253 q = 1) (hb : d198467 q = 1) : d200723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16254 q = 1) (hb : d198467 q = 1) : d200724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16254, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16254, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53410 (p : Pattern) (ha : d16343 p = 1) (hb : d198467 p = 1) : d200813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d198467 q = 1) : d200709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53406 q ha hb
    | true =>
      simp only [d16240, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53396 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d198467 q = 1) : d200710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d198467 q = 1) : d200711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d198467 q = 1) : d200712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d198467 q = 1) : d200713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d198467 q = 1) : d200808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53396 q ha hb
    | true =>
      simp only [d939, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d198467 q = 1) : d200809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d198467 q = 1) : d200810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d198467 q = 1) : d200811 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d198467 q = 1) : d200812 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16343 q = 1) (hb : d198467 q = 1) : d200813 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16343, d200813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16343, d200813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53411 (p : Pattern) (ha : d806 p = 1) (hb : d198467 p = 1) : d200731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d198467 q = 1) : d200706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d198467 q = 1) : d200730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d200730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d200730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d198467 q = 1) : d200731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d200731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d200731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53412 (p : Pattern) (ha : d816 p = 1) (hb : d198467 p = 1) : d200741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d198467 q = 1) : d200739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d200739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d200739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d198467 q = 1) : d200740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d200740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d200740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d198467 q = 1) : d200741 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d200741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d200741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53413 (p : Pattern) (ha : d16259 p = 1) (hb : d198467 p = 1) : d200729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53405 q ha hb
    | true =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d198467 q = 1) : d200702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d198467 q = 1) : d200728 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d200728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d200728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16259 q = 1) (hb : d198467 q = 1) : d200729 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16259, d200729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16259, d200729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53414 (p : Pattern) (ha : d16266 p = 1) (hb : d198467 p = 1) : d200738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53405 q ha hb
    | true =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d198467 q = 1) : d200736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d200736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d200736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d198467 q = 1) : d200737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d200737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d200737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16266 q = 1) (hb : d198467 q = 1) : d200738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16266, d200738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16266, d200738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53415 (p : Pattern) (ha : d833 p = 1) (hb : d198467 p = 1) : d200745 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d829 q = 1) : d829 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d538 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d830 q = 1) (hb : d152852 q = 1) : d25761 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d831 q = 1) (hb : d152852 q = 1) : d25762 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d831, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d831, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d832 q = 1) (hb : d152852 q = 1) : d25763 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d832, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d832, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d541 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d833 q = 1) (hb : d198467 q = 1) : d200745 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d833, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d833, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53416 (p : Pattern) (ha : d9586 p = 1) (hb : d198467 p = 1) : d200517 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d538 q = 1) : d538 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d539 q = 1) (hb : d152852 q = 1) : d25429 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d540 q = 1) (hb : d152852 q = 1) : d25430 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d25430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d540, d25430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d541 q = 1) (hb : d152852 q = 1) : d25431 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d25431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d541, d25431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9585 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9586 q = 1) (hb : d198467 q = 1) : d200517 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9586, d198467, d200517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9586, d198467, d200517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53417 (p : Pattern) (ha : d9596 p = 1) (hb : d198467 p = 1) : d200751 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d532 q = 1) : d532 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9593 q = 1) (hb : d152852 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9593, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9593, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9594 q = 1) (hb : d152852 q = 1) : d25781 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9594, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9594, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9595 q = 1) (hb : d152852 q = 1) : d25782 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9595, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9595, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9585 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9596 q = 1) (hb : d198467 q = 1) : d200751 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9596, d198467, d200751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9596, d198467, d200751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro53418 (p : Pattern) (ha : d16274 p = 1) (hb : d198467 p = 1) : d200757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d198467 q = 1) : d200746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53415 q ha hb
    | true =>
      simp only [d834, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d198467 q = 1) : d200747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d198467 q = 1) : d200748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d198467 q = 1) : d200749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9587 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53416 q ha hb
    | true =>
      simp only [d9587, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9589 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9589, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16270 q = 1) (hb : d198467 q = 1) : d200520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16270, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16270, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16271 q = 1) (hb : d198467 q = 1) : d200521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16271, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16271, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16272 q = 1) (hb : d198467 q = 1) : d200750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16272, d200750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16272, d200750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9597 q = 1) (hb : d198467 q = 1) : d200752 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53417 q ha hb
    | true =>
      simp only [d9597, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9599 q = 1) (hb : d198467 q = 1) : d200753 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9599, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14529 q = 1) (hb : d198467 q = 1) : d200754 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14529, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14529, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14530 q = 1) (hb : d198467 q = 1) : d200755 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14530, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14530, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9468 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
    | true =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9470 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12748 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12749 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12749, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16273 q = 1) (hb : d198467 q = 1) : d200756 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16273, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16273, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16274 q = 1) (hb : d198467 q = 1) : d200757 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16274, d200757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16274, d200757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro53419 (p : Pattern) (ha : d16278 p = 1) (hb : d198467 p = 1) : d200761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9468 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
    | true =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9470 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12748 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12749 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12749, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12750 q = 1) (hb : d198467 q = 1) : d200682 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12750, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d198467 q = 1) : d25698 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16278 q = 1) (hb : d198467 q = 1) : d200761 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16278, d200761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16278, d200761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53420 (p : Pattern) (ha : d16284 p = 1) (hb : d198467 p = 1) : d200767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16275 q = 1) (hb : d198467 q = 1) : d200758 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d200758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53418 q ha hb
    | true =>
      simp only [d16275, d200758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53404 q ha hb
  have h2 (q : Pattern) (ha : d16276 q = 1) (hb : d198467 q = 1) : d200759 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16276, d200759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16276, d200759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16277 q = 1) (hb : d198467 q = 1) : d200760 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16277, d200760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16277, d200760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16279 q = 1) (hb : d198467 q = 1) : d200762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d200762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53404 q ha hb
    | true =>
      simp only [d16279, d200762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53419 q ha hb
  have h5 (q : Pattern) (ha : d16280 q = 1) (hb : d198467 q = 1) : d200763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16280, d200763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16280, d200763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16281 q = 1) (hb : d198467 q = 1) : d200764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16281, d200764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16281, d200764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16282 q = 1) (hb : d198467 q = 1) : d200765 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16282, d200765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16282, d200765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16228 q = 1) (hb : d198467 q = 1) : d200685 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53404 q ha hb
    | true =>
      simp only [d16228, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53394 q ha hb
  have h9 (q : Pattern) (ha : d16229 q = 1) (hb : d198467 q = 1) : d200686 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16230 q = 1) (hb : d198467 q = 1) : d200687 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d763 q = 1) (hb : d198467 q = 1) : d200688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53394 q ha hb
    | true =>
      simp only [d763, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47182 q ha hb
  have h12 (q : Pattern) (ha : d764 q = 1) (hb : d198467 q = 1) : d200689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d765 q = 1) (hb : d198467 q = 1) : d200690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16231 q = 1) (hb : d198467 q = 1) : d200691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16231, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16283 q = 1) (hb : d198467 q = 1) : d200766 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16283, d200766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16283, d200766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16284 q = 1) (hb : d198467 q = 1) : d200767 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16284, d200767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16284, d200767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro53421 (p : Pattern) (ha : d16290 p = 1) (hb : d198467 p = 1) : d200773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d198467 q = 1) : d200768 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d200768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53420 q ha hb
    | true =>
      simp only [d16285, d200768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d198467 q = 1) : d200769 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d200769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d200769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53405 q ha hb
    | true =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d198467 q = 1) : d200770 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d200770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d200770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d198467 q = 1) : d200771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d200771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d200771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d198467 q = 1) : d200772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d200772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d200772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16290 q = 1) (hb : d198467 q = 1) : d200773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16290, d200773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16290, d200773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53422 (p : Pattern) (ha : d16314 p = 1) (hb : d198467 p = 1) : d200779 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53405 q ha hb
    | true =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d198467 q = 1) : d200776 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d200776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d200776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d198467 q = 1) : d200777 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d200777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d200777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d198467 q = 1) : d200778 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d200778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d200778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16314 q = 1) (hb : d198467 q = 1) : d200779 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16314, d200779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16314, d200779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53423 (p : Pattern) (ha : d128274 p = 1) (hb : d198467 p = 1) : d200785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d198467 q = 1) : d200732 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d200732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53413 q ha hb
    | true =>
      simp only [d16260, d200732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53411 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d198467 q = 1) : d200733 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d200733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d200733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d198467 q = 1) : d200734 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d200734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d200734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d198467 q = 1) : d200735 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d200735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d200735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d198467 q = 1) : d200742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d200742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53414 q ha hb
    | true =>
      simp only [d16267, d200742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53412 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d198467 q = 1) : d200743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d200743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d200743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d198467 q = 1) : d200744 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d200744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d200744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d198467 q = 1) : d200774 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d200774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53421 q ha hb
    | true =>
      simp only [d16291, d200774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53406 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d198467 q = 1) : d200775 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d200775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d200775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d198467 q = 1) : d200780 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d200780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53422 q ha hb
    | true =>
      simp only [d16315, d200780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d198467 q = 1) : d200781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d200781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d200781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d198467 q = 1) : d200782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d200782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d200782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d198467 q = 1) : d200783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d200783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d200783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d198467 q = 1) : d200784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d200784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d200784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128274 q = 1) (hb : d198467 q = 1) : d200785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128274, d200785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128274, d200785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53424 (p : Pattern) (ha : d916 p = 1) (hb : d198467 p = 1) : d200787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d198467 q = 1) : d200706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d198467 q = 1) : d200730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d200730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d200730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d198467 q = 1) : d200787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d200787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d200787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53425 (p : Pattern) (ha : d922 p = 1) (hb : d198467 p = 1) : d200793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d198467 q = 1) : d200739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d200739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d200739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d198467 q = 1) : d200740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d200740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d200740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d198467 q = 1) : d200793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d200793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d200793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53426 (p : Pattern) (ha : d16321 p = 1) (hb : d198467 p = 1) : d200786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53405 q ha hb
    | true =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d198467 q = 1) : d200702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d198467 q = 1) : d200728 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d200728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d200728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16321 q = 1) (hb : d198467 q = 1) : d200786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16321, d200786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16321, d200786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53427 (p : Pattern) (ha : d16326 p = 1) (hb : d198467 p = 1) : d200792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53405 q ha hb
    | true =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53395 q ha hb
    | true =>
      simp only [d774, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d198467 q = 1) : d200736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d200736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d200736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d198467 q = 1) : d200737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d200737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d200737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16326 q = 1) (hb : d198467 q = 1) : d200792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16326, d200792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16326, d200792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53428 (p : Pattern) (ha : d16330 p = 1) (hb : d198467 p = 1) : d200797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d198467 q = 1) : d200768 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d200768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53420 q ha hb
    | true =>
      simp only [d16285, d200768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d198467 q = 1) : d200769 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d200769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d200769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53405 q ha hb
    | true =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d198467 q = 1) : d200770 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d200770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d200770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d198467 q = 1) : d200771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d200771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d200771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d198467 q = 1) : d200772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d200772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d200772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16330 q = 1) (hb : d198467 q = 1) : d200797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16330, d200797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16330, d200797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53429 (p : Pattern) (ha : d16335 p = 1) (hb : d198467 p = 1) : d200800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53405 q ha hb
    | true =>
      simp only [d16234, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d198467 q = 1) : d200776 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d200776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d200776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d198467 q = 1) : d200777 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d200777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d200777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d198467 q = 1) : d200778 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d200778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d200778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16335 q = 1) (hb : d198467 q = 1) : d200800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16335, d200800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16335, d200800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53430 (p : Pattern) (ha : d128279 p = 1) (hb : d198467 p = 1) : d200806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d198467 q = 1) : d200732 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d200732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53413 q ha hb
    | true =>
      simp only [d16260, d200732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53411 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d198467 q = 1) : d200733 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d200733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d200733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d198467 q = 1) : d200734 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d200734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d200734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d198467 q = 1) : d200735 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d200735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d200735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d198467 q = 1) : d200742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d200742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53414 q ha hb
    | true =>
      simp only [d16267, d200742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53412 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d198467 q = 1) : d200743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d200743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d200743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d198467 q = 1) : d200744 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d200744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d200744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d198467 q = 1) : d200774 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d200774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53421 q ha hb
    | true =>
      simp only [d16291, d200774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53406 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d198467 q = 1) : d200775 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d200775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d200775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d198467 q = 1) : d200780 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d200780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53422 q ha hb
    | true =>
      simp only [d16315, d200780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d198467 q = 1) : d200781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d200781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d200781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d198467 q = 1) : d200782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d200782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d200782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d198467 q = 1) : d200783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d200783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d200783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d198467 q = 1) : d200784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d200784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d200784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16322 q = 1) (hb : d198467 q = 1) : d200788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16322, d200788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53426 q ha hb
    | true =>
      simp only [d16322, d200788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53424 q ha hb
  have h16 (q : Pattern) (ha : d16323 q = 1) (hb : d198467 q = 1) : d200789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16323, d200789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16323, d200789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16324 q = 1) (hb : d198467 q = 1) : d200790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16324, d200790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16324, d200790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16325 q = 1) (hb : d198467 q = 1) : d200791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16325, d200791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16325, d200791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16327 q = 1) (hb : d198467 q = 1) : d200794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16327, d200794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53427 q ha hb
    | true =>
      simp only [d16327, d200794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53425 q ha hb
  have h20 (q : Pattern) (ha : d16328 q = 1) (hb : d198467 q = 1) : d200795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16328, d200795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16328, d200795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16329 q = 1) (hb : d198467 q = 1) : d200796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16329, d200796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16329, d200796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16331 q = 1) (hb : d198467 q = 1) : d200798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d200798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53428 q ha hb
    | true =>
      simp only [d16331, d200798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53408 q ha hb
  have h23 (q : Pattern) (ha : d128275 q = 1) (hb : d198467 q = 1) : d200799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d200799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128275, d200799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16336 q = 1) (hb : d198467 q = 1) : d200801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d200801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53429 q ha hb
    | true =>
      simp only [d16336, d200801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16337 q = 1) (hb : d198467 q = 1) : d200802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d200802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16337, d200802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128276 q = 1) (hb : d198467 q = 1) : d200803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d200803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128276, d200803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128277 q = 1) (hb : d198467 q = 1) : d200804 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128277, d200804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128277, d200804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128278 q = 1) (hb : d198467 q = 1) : d200805 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128278, d200805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128278, d200805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128279 q = 1) (hb : d198467 q = 1) : d200806 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128279, d200806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128279, d200806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro53431 (p : Pattern) (ha : d128286 p = 1) (hb : d198467 p = 1) : d200826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16331 q = 1) (hb : d198467 q = 1) : d200798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d200798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53428 q ha hb
    | true =>
      simp only [d16331, d200798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53408 q ha hb
  have h2 (q : Pattern) (ha : d128275 q = 1) (hb : d198467 q = 1) : d200799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d200799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128275, d200799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16336 q = 1) (hb : d198467 q = 1) : d200801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d200801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53429 q ha hb
    | true =>
      simp only [d16336, d200801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16337 q = 1) (hb : d198467 q = 1) : d200802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d200802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16337, d200802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128276 q = 1) (hb : d198467 q = 1) : d200803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d200803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128276, d200803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128284 q = 1) (hb : d198467 q = 1) : d200824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128284, d200824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128284, d200824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128285 q = 1) (hb : d198467 q = 1) : d200825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128285, d200825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128285, d200825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128286 q = 1) (hb : d198467 q = 1) : d200826 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d200826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d200826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53432 (p : Pattern) (ha : d16362 p = 1) (hb : d198467 p = 1) : d200844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d198467 q = 1) : d200834 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d200834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d200834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53415 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d198467 q = 1) : d200746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53415 q ha hb
    | true =>
      simp only [d834, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d198467 q = 1) : d200835 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d200835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d200835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d198467 q = 1) : d200747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d198467 q = 1) : d200836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d200836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d200836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d198467 q = 1) : d200837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d200837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d200837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16356 q = 1) (hb : d198467 q = 1) : d200606 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16356, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53416 q ha hb
  have h8 (q : Pattern) (ha : d9587 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53416 q ha hb
    | true =>
      simp only [d9587, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16357 q = 1) (hb : d198467 q = 1) : d200607 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16357, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9589 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9589, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16358 q = 1) (hb : d198467 q = 1) : d200608 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16358, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16358, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16359 q = 1) (hb : d198467 q = 1) : d200609 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16359, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16359, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16360 q = 1) (hb : d198467 q = 1) : d200838 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16360, d200838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16360, d200838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14644 q = 1) (hb : d198467 q = 1) : d200839 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d200839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14644, d200839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53417 q ha hb
  have h15 (q : Pattern) (ha : d9597 q = 1) (hb : d198467 q = 1) : d200752 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53417 q ha hb
    | true =>
      simp only [d9597, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14645 q = 1) (hb : d198467 q = 1) : d200840 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d200840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14645, d200840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9599 q = 1) (hb : d198467 q = 1) : d200753 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9599, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14646 q = 1) (hb : d198467 q = 1) : d200841 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14646, d200841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14646, d200841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14647 q = 1) (hb : d198467 q = 1) : d200842 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14647, d200842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d14647, d200842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12858 q = 1) (hb : d198467 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
  have h21 (q : Pattern) (ha : d9468 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
    | true =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12859 q = 1) (hb : d198467 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12859, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9470 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12860 q = 1) (hb : d198467 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12860, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12861 q = 1) (hb : d198467 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12861, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16361 q = 1) (hb : d198467 q = 1) : d200843 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16361, d200843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16361, d200843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16362 q = 1) (hb : d198467 q = 1) : d200844 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16362, d200844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16362, d200844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro53433 (p : Pattern) (ha : d16363 p = 1) (hb : d198467 p = 1) : d200846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d198467 q = 1) : d200606 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53367 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53367 q ha hb
    | true =>
      simp only [d543, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d198467 q = 1) : d200607 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d198467 q = 1) : d200608 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d198467 q = 1) : d200609 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16156 q = 1) (hb : d198467 q = 1) : d200417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53368 q ha hb
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53368 q ha hb
    | true =>
      simp only [d9458, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d198467 q = 1) : d200418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16157, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9460 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9460, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16158 q = 1) (hb : d198467 q = 1) : d200419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16158, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16159 q = 1) (hb : d198467 q = 1) : d200420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16159, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16160 q = 1) (hb : d198467 q = 1) : d200610 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d200610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16160, d200610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12858 q = 1) (hb : d198467 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
  have h15 (q : Pattern) (ha : d9468 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
    | true =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12859 q = 1) (hb : d198467 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12859, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9470 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12860 q = 1) (hb : d198467 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12860, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12861 q = 1) (hb : d198467 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12861, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d971 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
  have h21 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d972 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d973 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d974 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12862 q = 1) (hb : d198467 q = 1) : d200845 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d200845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12862, d200845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16363 q = 1) (hb : d198467 q = 1) : d200846 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16363, d200846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16363, d200846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro53434 (p : Pattern) (ha : d16367 p = 1) (hb : d198467 p = 1) : d200850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12858 q = 1) (hb : d198467 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53369 q ha hb
    | true =>
      simp only [d9468, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12859 q = 1) (hb : d198467 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12859, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9470 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9470, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12860 q = 1) (hb : d198467 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12860, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12861 q = 1) (hb : d198467 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12861, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47100 q ha hb
    | true =>
      simp only [d751, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12862 q = 1) (hb : d198467 q = 1) : d200845 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d200845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12862, d200845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d198467 q = 1) : d25957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16367 q = 1) (hb : d198467 q = 1) : d200850 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16367, d200850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16367, d200850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53435 (p : Pattern) (ha : d16377 p = 1) (hb : d198467 p = 1) : d200864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16364 q = 1) (hb : d198467 q = 1) : d200847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16364, d200847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53432 q ha hb
    | true =>
      simp only [d16364, d200847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53433 q ha hb
  have h2 (q : Pattern) (ha : d16365 q = 1) (hb : d198467 q = 1) : d200848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d200848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16365, d200848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16366 q = 1) (hb : d198467 q = 1) : d200849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, d200849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, d200849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16368 q = 1) (hb : d198467 q = 1) : d200851 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16368, d200851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53433 q ha hb
    | true =>
      simp only [d16368, d200851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53434 q ha hb
  have h5 (q : Pattern) (ha : d16369 q = 1) (hb : d198467 q = 1) : d200852 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d200852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16369, d200852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16370 q = 1) (hb : d198467 q = 1) : d200853 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, d200853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, d200853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16371 q = 1) (hb : d198467 q = 1) : d200854 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, d200854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16371, d200854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16372 q = 1) (hb : d198467 q = 1) : d200856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d200856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53433 q ha hb
    | true =>
      simp only [d16372, d200856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53400 q ha hb
  have h9 (q : Pattern) (ha : d16373 q = 1) (hb : d198467 q = 1) : d200857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d200857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d200857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16374 q = 1) (hb : d198467 q = 1) : d200858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d200858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d200858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d987 q = 1) (hb : d198467 q = 1) : d200859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53400 q ha hb
    | true =>
      simp only [d987, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47196 q ha hb
  have h12 (q : Pattern) (ha : d988 q = 1) (hb : d198467 q = 1) : d200860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d989 q = 1) (hb : d198467 q = 1) : d200861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16375 q = 1) (hb : d198467 q = 1) : d200862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d200862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16375, d200862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16376 q = 1) (hb : d198467 q = 1) : d200863 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, d200863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16376, d200863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16377 q = 1) (hb : d198467 q = 1) : d200864 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16377, d200864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16377, d200864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro53436 (p : Pattern) (ha : d16381 p = 1) (hb : d198467 p = 1) : d200869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16372 q = 1) (hb : d198467 q = 1) : d200856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d200856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53433 q ha hb
    | true =>
      simp only [d16372, d200856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53400 q ha hb
  have h2 (q : Pattern) (ha : d16373 q = 1) (hb : d198467 q = 1) : d200857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d200857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d200857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16374 q = 1) (hb : d198467 q = 1) : d200858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d200858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d200858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d198467 q = 1) : d200859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53400 q ha hb
    | true =>
      simp only [d987, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47196 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d198467 q = 1) : d200860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d198467 q = 1) : d200861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16375 q = 1) (hb : d198467 q = 1) : d200862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d200862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16375, d200862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d198467 q = 1) : d200867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d200867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d200867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16380 q = 1) (hb : d198467 q = 1) : d200868 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, d200868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16380, d200868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16381 q = 1) (hb : d198467 q = 1) : d200869 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16381, d200869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16381, d200869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro53437 (p : Pattern) (ha : d16387 p = 1) (hb : d198467 p = 1) : d200875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16378 q = 1) (hb : d198467 q = 1) : d200865 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16378, d200865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53435 q ha hb
    | true =>
      simp only [d16378, d200865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16379 q = 1) (hb : d198467 q = 1) : d200866 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16379, d200866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16379, d200866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16382 q = 1) (hb : d198467 q = 1) : d200870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53436 q ha hb
    | true =>
      simp only [d16382, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16383 q = 1) (hb : d198467 q = 1) : d200871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16384 q = 1) (hb : d198467 q = 1) : d200872 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16384, d200872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16384, d200872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16385 q = 1) (hb : d198467 q = 1) : d200873 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16385, d200873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16385, d200873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16386 q = 1) (hb : d198467 q = 1) : d200874 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16386, d200874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16386, d200874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16387 q = 1) (hb : d198467 q = 1) : d200875 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16387, d200875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16387, d200875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53438 (p : Pattern) (ha : d16391 p = 1) (hb : d198467 p = 1) : d200883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d198467 q = 1) : d200870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53436 q ha hb
    | true =>
      simp only [d16382, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d198467 q = 1) : d200871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d198467 q = 1) : d200878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d200878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53401 q ha hb
    | true =>
      simp only [d1006, d200878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d198467 q = 1) : d200879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d200879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d200879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16388 q = 1) (hb : d198467 q = 1) : d200880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16388, d200880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16388, d200880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16389 q = 1) (hb : d198467 q = 1) : d200881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16389, d200881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16389, d200881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16390 q = 1) (hb : d198467 q = 1) : d200882 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16390, d200882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16390, d200882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16391 q = 1) (hb : d198467 q = 1) : d200883 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16391, d200883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16391, d200883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53439 (p : Pattern) (ha : d16417 p = 1) (hb : d198467 p = 1) : d200889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d198467 q = 1) : d200870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53436 q ha hb
    | true =>
      simp only [d16382, d200870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d198467 q = 1) : d200871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d200871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16414 q = 1) (hb : d198467 q = 1) : d200886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16414, d200886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16414, d200886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16415 q = 1) (hb : d198467 q = 1) : d200887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16415, d200887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16415, d200887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16416 q = 1) (hb : d198467 q = 1) : d200888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16416, d200888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16416, d200888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16417 q = 1) (hb : d198467 q = 1) : d200889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16417, d200889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16417, d200889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53440 (p : Pattern) (ha : d128296 p = 1) (hb : d198467 p = 1) : d200895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16392 q = 1) (hb : d198467 q = 1) : d200884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16392, d200884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53437 q ha hb
    | true =>
      simp only [d16392, d200884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53438 q ha hb
  have h2 (q : Pattern) (ha : d128292 q = 1) (hb : d198467 q = 1) : d200885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d200885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128292, d200885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16418 q = 1) (hb : d198467 q = 1) : d200890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16418, d200890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53439 q ha hb
    | true =>
      simp only [d16418, d200890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16419 q = 1) (hb : d198467 q = 1) : d200891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16419, d200891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16419, d200891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d198467 q = 1) : d200892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d200892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128293, d200892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d198467 q = 1) : d200893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d200893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d200893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d198467 q = 1) : d200894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d200894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d200894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d198467 q = 1) : d200895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d200895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d200895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53441 (p : Pattern) (ha : d128302 p = 1) (hb : d198467 p = 1) : d200912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16246 q = 1) (hb : d198467 q = 1) : d200715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16246, d200715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16246, d200715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53407 q ha hb
  have h2 (q : Pattern) (ha : d16247 q = 1) (hb : d198467 q = 1) : d200716 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16247, d200716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16247, d200716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16255 q = 1) (hb : d198467 q = 1) : d200725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53407 q ha hb
    | true =>
      simp only [d16255, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53409 q ha hb
  have h4 (q : Pattern) (ha : d16256 q = 1) (hb : d198467 q = 1) : d200726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16256, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16257 q = 1) (hb : d198467 q = 1) : d200727 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16257, d200727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16257, d200727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128280 q = 1) (hb : d198467 q = 1) : d200807 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128280, d200807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53423 q ha hb
    | true =>
      simp only [d128280, d200807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53430 q ha hb
  have h7 (q : Pattern) (ha : d16344 q = 1) (hb : d198467 q = 1) : d200820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16344, d200820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53410 q ha hb
    | true =>
      simp only [d16344, d200820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53398 q ha hb
  have h8 (q : Pattern) (ha : d128281 q = 1) (hb : d198467 q = 1) : d200821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128281, d200821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128281, d200821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128282 q = 1) (hb : d198467 q = 1) : d200822 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128282, d200822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128282, d200822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128283 q = 1) (hb : d198467 q = 1) : d200823 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128283, d200823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128283, d200823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128287 q = 1) (hb : d198467 q = 1) : d200827 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d200827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128287, d200827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53431 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d198467 q = 1) : d200829 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d200829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d200829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53399 q ha hb
  have h13 (q : Pattern) (ha : d128288 q = 1) (hb : d198467 q = 1) : d200830 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d200830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128288, d200830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128289 q = 1) (hb : d198467 q = 1) : d200831 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d200831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128289, d200831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128290 q = 1) (hb : d198467 q = 1) : d200832 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d200832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128290, d200832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128291 q = 1) (hb : d198467 q = 1) : d200833 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128291, d200833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128291, d200833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128297 q = 1) (hb : d198467 q = 1) : d200896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d200896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128297, d200896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53440 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d198467 q = 1) : d200907 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d200907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d200907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53403 q ha hb
  have h19 (q : Pattern) (ha : d128298 q = 1) (hb : d198467 q = 1) : d200908 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d200908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128298, d200908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128299 q = 1) (hb : d198467 q = 1) : d200909 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d200909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128299, d200909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128300 q = 1) (hb : d198467 q = 1) : d200910 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d200910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128300, d200910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128301 q = 1) (hb : d198467 q = 1) : d200911 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d200911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128301, d200911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128302 q = 1) (hb : d198467 q = 1) : d200912 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d200912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128302, d200912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro53442 (p : Pattern) (ha : d128308 p = 1) (hb : d198467 p = 1) : d200918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d198467 q = 1) : d200913 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d200913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d200913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53441 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d198467 q = 1) : d200914 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d200914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d200914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d198467 q = 1) : d200915 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d200915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d200915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d198467 q = 1) : d200916 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d200916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d200916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d198467 q = 1) : d200917 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d200917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d200917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d198467 q = 1) : d200918 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d200918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d200918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53443 (p : Pattern) (ha : d5017 p = 1) (hb : d198467 p = 1) : d200932 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1095 q = 1) : d1095 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5014 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5014, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5014, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d5015 q = 1) (hb : d152852 q = 1) : d26105 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5015, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5015, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5016 q = 1) (hb : d152852 q = 1) : d26106 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5016, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5016, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1119 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5017 q = 1) (hb : d198467 q = 1) : d200932 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5017, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5017, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53444 (p : Pattern) (ha : d14773 p = 1) (hb : d198467 p = 1) : d200945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5018 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53443 q ha hb
    | true =>
      simp only [d5018, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5019 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5019, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5020 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5020, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5020, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5021 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5021, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5021, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5022 q = 1) (hb : d198467 q = 1) : d200940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5022, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d198467 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14773 q = 1) (hb : d198467 q = 1) : d200945 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14773, d200945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14773, d200945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53445 (p : Pattern) (ha : d1120 p = 1) (hb : d198467 p = 1) : d200932 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1107 q = 1) (hb : d152852 q = 1) : d26105 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1107, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1107, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1108 q = 1) (hb : d152852 q = 1) : d26106 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1108, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1108, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1119 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1120 q = 1) (hb : d198467 q = 1) : d200932 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1120, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1120, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53446 (p : Pattern) (ha : d14778 p = 1) (hb : d198467 p = 1) : d200945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53445 q ha hb
    | true =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d198467 q = 1) : d200940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d198467 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14778 q = 1) (hb : d198467 q = 1) : d200945 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14778, d200945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14778, d200945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53447 (p : Pattern) (ha : d1099 p = 1) (hb : d198467 p = 1) : d200745 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d829 q = 1) : d829 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d538 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d830 q = 1) (hb : d152852 q = 1) : d25761 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1091 q = 1) (hb : d152852 q = 1) : d25762 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1091, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1091, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1092 q = 1) (hb : d152852 q = 1) : d25763 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1092, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1092, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1098 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1099 q = 1) (hb : d198467 q = 1) : d200745 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1099, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1099, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53448 (p : Pattern) (ha : d9777 p = 1) (hb : d198467 p = 1) : d200927 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1089 q = 1) : d1089 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9768 q = 1) (hb : d152852 q = 1) : d26079 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9768, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9768, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9769 q = 1) (hb : d152852 q = 1) : d26098 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9769, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9769, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9770 q = 1) (hb : d152852 q = 1) : d26099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9770, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9770, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9776 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9777 q = 1) (hb : d198467 q = 1) : d200927 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9777, d198467, d200927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9777, d198467, d200927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro53449 (p : Pattern) (ha : d9788 p = 1) (hb : d198467 p = 1) : d200921 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d538 q = 1) : d538 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d539 q = 1) (hb : d152852 q = 1) : d25429 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1097 q = 1) (hb : d152852 q = 1) : d26087 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d26087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1097, d26087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1098 q = 1) (hb : d152852 q = 1) : d26088 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d26088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1098, d26088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9776 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9788 q = 1) (hb : d198467 q = 1) : d200921 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9788, d198467, d200921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9788, d198467, d200921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53450 (p : Pattern) (ha : d9799 p = 1) (hb : d198467 p = 1) : d200932 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1095 q = 1) : d1095 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9795 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9795, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9795, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d9796 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9797 q = 1) (hb : d152852 q = 1) : d26105 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9797, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9797, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9798 q = 1) (hb : d152852 q = 1) : d26106 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9798, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9798, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1119 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9799 q = 1) (hb : d198467 q = 1) : d200932 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9799, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9799, d198467, d200932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro53451 (p : Pattern) (ha : d16442 p = 1) (hb : d198467 p = 1) : d200938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d198467 q = 1) : d200746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53447 q ha hb
    | true =>
      simp only [d1100, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d198467 q = 1) : d200747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d198467 q = 1) : d200748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d198467 q = 1) : d200749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9789 q = 1) (hb : d198467 q = 1) : d200922 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53449 q ha hb
    | true =>
      simp only [d9789, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9791 q = 1) (hb : d198467 q = 1) : d200923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9791, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16438 q = 1) (hb : d198467 q = 1) : d200924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16438, d200924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16438, d200924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16439 q = 1) (hb : d198467 q = 1) : d200925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16439, d200925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16439, d200925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16440 q = 1) (hb : d198467 q = 1) : d200926 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16440, d200926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16440, d200926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9778 q = 1) (hb : d198467 q = 1) : d200928 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53448 q ha hb
    | true =>
      simp only [d9778, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9780 q = 1) (hb : d198467 q = 1) : d200929 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9780, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14758 q = 1) (hb : d198467 q = 1) : d200930 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14758, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14759 q = 1) (hb : d198467 q = 1) : d200931 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14759, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9800 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53450 q ha hb
    | true =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9802 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14763 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14764 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14764, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16441 q = 1) (hb : d198467 q = 1) : d200937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16441, d200937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16441, d200937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16442 q = 1) (hb : d198467 q = 1) : d200938 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16442, d200938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16442, d200938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro53452 (p : Pattern) (ha : d1109 p = 1) (hb : d198467 p = 1) : d200921 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d538 q = 1) : d538 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d539 q = 1) (hb : d152852 q = 1) : d25429 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1097 q = 1) (hb : d152852 q = 1) : d26087 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d26087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1097, d26087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1098 q = 1) (hb : d152852 q = 1) : d26088 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d26088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1098, d26088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1108 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1109 q = 1) (hb : d198467 q = 1) : d200921 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1109, d198467, d200921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1109, d198467, d200921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53453 (p : Pattern) (ha : d16443 p = 1) (hb : d198467 p = 1) : d200941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d198467 q = 1) : d200922 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53452 q ha hb
    | true =>
      simp only [d1110, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d198467 q = 1) : d200923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d198467 q = 1) : d200924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d200924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d200924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d198467 q = 1) : d200925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d200925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d200925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53445 q ha hb
    | true =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d198467 q = 1) : d200939 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d200939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d200939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9800 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53450 q ha hb
    | true =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9802 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14763 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14764 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14764, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d14765 q = 1) (hb : d198467 q = 1) : d200940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14765, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16443 q = 1) (hb : d198467 q = 1) : d200941 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16443, d200941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16443, d200941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53454 (p : Pattern) (ha : d16456 p = 1) (hb : d198467 p = 1) : d200952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d198467 q = 1) : d200942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d200942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53451 q ha hb
    | true =>
      simp only [d16444, d200942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53453 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d198467 q = 1) : d200943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d200943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d200943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d198467 q = 1) : d200944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d200944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d200944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d198467 q = 1) : d200946 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53453 q ha hb
    | true =>
      simp only [d16447, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53444 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d198467 q = 1) : d200947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d198467 q = 1) : d200948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d198467 q = 1) : d200949 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d200949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d200949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16451 q = 1) (hb : d198467 q = 1) : d200946 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53453 q ha hb
    | true =>
      simp only [d16451, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53446 q ha hb
  have h9 (q : Pattern) (ha : d16452 q = 1) (hb : d198467 q = 1) : d200947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16453 q = 1) (hb : d198467 q = 1) : d200948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16454 q = 1) (hb : d198467 q = 1) : d200950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d200950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16454, d200950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16455 q = 1) (hb : d198467 q = 1) : d200951 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16455, d200951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16455, d200951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16456 q = 1) (hb : d198467 q = 1) : d200952 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16456, d200952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16456, d200952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53455 (p : Pattern) (ha : d16460 p = 1) (hb : d198467 p = 1) : d200956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16451 q = 1) (hb : d198467 q = 1) : d200946 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53453 q ha hb
    | true =>
      simp only [d16451, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53446 q ha hb
  have h2 (q : Pattern) (ha : d16452 q = 1) (hb : d198467 q = 1) : d200947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16453 q = 1) (hb : d198467 q = 1) : d200948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16454 q = 1) (hb : d198467 q = 1) : d200950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d200950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16454, d200950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16459 q = 1) (hb : d198467 q = 1) : d200955 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16459, d200955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16459, d200955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16460 q = 1) (hb : d198467 q = 1) : d200956 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16460, d200956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16460, d200956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53456 (p : Pattern) (ha : d16466 p = 1) (hb : d198467 p = 1) : d200962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53454 q ha hb
    | true =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d198467 q = 1) : d200959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d198467 q = 1) : d200960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d198467 q = 1) : d200961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16466 q = 1) (hb : d198467 q = 1) : d200962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16466, d200962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16466, d200962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53457 (p : Pattern) (ha : d16470 p = 1) (hb : d198467 p = 1) : d200966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d198467 q = 1) : d200963 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d198467 q = 1) : d200964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d198467 q = 1) : d200965 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d200965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d200965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16470 q = 1) (hb : d198467 q = 1) : d200966 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16470, d200966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16470, d200966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53458 (p : Pattern) (ha : d16476 p = 1) (hb : d198467 p = 1) : d200972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d198467 q = 1) : d200967 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53456 q ha hb
    | true =>
      simp only [d16471, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53457 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d198467 q = 1) : d200968 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d198467 q = 1) : d200969 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d198467 q = 1) : d200970 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d198467 q = 1) : d200971 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16476 q = 1) (hb : d198467 q = 1) : d200972 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16476, d200972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16476, d200972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53459 (p : Pattern) (ha : d16479 p = 1) (hb : d198467 p = 1) : d200975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53454 q ha hb
    | true =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d198467 q = 1) : d200959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d198467 q = 1) : d200960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d198467 q = 1) : d200961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16479 q = 1) (hb : d198467 q = 1) : d200975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16479, d200975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16479, d200975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53460 (p : Pattern) (ha : d16480 p = 1) (hb : d198467 p = 1) : d200976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d198467 q = 1) : d200963 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d198467 q = 1) : d200964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d198467 q = 1) : d200965 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d200965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d200965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16480 q = 1) (hb : d198467 q = 1) : d200976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16480, d200976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16480, d200976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53461 (p : Pattern) (ha : d16486 p = 1) (hb : d198467 p = 1) : d200982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d198467 q = 1) : d200967 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53456 q ha hb
    | true =>
      simp only [d16471, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53457 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d198467 q = 1) : d200968 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d198467 q = 1) : d200969 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d198467 q = 1) : d200970 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d198467 q = 1) : d200971 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16481 q = 1) (hb : d198467 q = 1) : d200977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53459 q ha hb
    | true =>
      simp only [d16481, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53460 q ha hb
  have h7 (q : Pattern) (ha : d16482 q = 1) (hb : d198467 q = 1) : d200978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16483 q = 1) (hb : d198467 q = 1) : d200979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16483, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16484 q = 1) (hb : d198467 q = 1) : d200980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16485 q = 1) (hb : d198467 q = 1) : d200981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16486 q = 1) (hb : d198467 q = 1) : d200982 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16486, d200982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16486, d200982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53462 (p : Pattern) (ha : d16527 p = 1) (hb : d198467 p = 1) : d200952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d198467 q = 1) : d200942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d200942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53451 q ha hb
    | true =>
      simp only [d16444, d200942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53453 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d198467 q = 1) : d200943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d200943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d200943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d198467 q = 1) : d200944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d200944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d200944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d198467 q = 1) : d200946 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53453 q ha hb
    | true =>
      simp only [d16447, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53444 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d198467 q = 1) : d200947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d198467 q = 1) : d200948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d198467 q = 1) : d200949 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d200949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d200949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16525 q = 1) (hb : d198467 q = 1) : d200950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16525, d200950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16525, d200950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16526 q = 1) (hb : d198467 q = 1) : d200951 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16526, d200951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16526, d200951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16527 q = 1) (hb : d198467 q = 1) : d200952 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16527, d200952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16527, d200952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro53463 (p : Pattern) (ha : d16537 p = 1) (hb : d198467 p = 1) : d200962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53462 q ha hb
    | true =>
      simp only [d16528, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d198467 q = 1) : d200959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d198467 q = 1) : d200960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d198467 q = 1) : d200961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16537 q = 1) (hb : d198467 q = 1) : d200962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16537, d200962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16537, d200962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53464 (p : Pattern) (ha : d16628 p = 1) (hb : d198467 p = 1) : d201075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16618 q = 1) (hb : d198467 q = 1) : d200967 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16618, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53463 q ha hb
    | true =>
      simp only [d16618, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53457 q ha hb
  have h2 (q : Pattern) (ha : d16619 q = 1) (hb : d198467 q = 1) : d200968 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16619, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16619, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16620 q = 1) (hb : d198467 q = 1) : d200969 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16620, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16620, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16621 q = 1) (hb : d198467 q = 1) : d200970 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16621, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16621, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16622 q = 1) (hb : d198467 q = 1) : d200971 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16622, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16622, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16623 q = 1) (hb : d198467 q = 1) : d201070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d201070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53457 q ha hb
    | true =>
      simp only [d16623, d201070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16624 q = 1) (hb : d198467 q = 1) : d201071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d201071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d201071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16625 q = 1) (hb : d198467 q = 1) : d201072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d201072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16625, d201072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16626 q = 1) (hb : d198467 q = 1) : d201073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d201073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d201073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16627 q = 1) (hb : d198467 q = 1) : d201074 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d201074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d201074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16628 q = 1) (hb : d198467 q = 1) : d201075 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16628, d201075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16628, d201075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53465 (p : Pattern) (ha : d16634 p = 1) (hb : d198467 p = 1) : d201081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16623 q = 1) (hb : d198467 q = 1) : d201070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d201070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53457 q ha hb
    | true =>
      simp only [d16623, d201070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16624 q = 1) (hb : d198467 q = 1) : d201071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d201071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d201071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16625 q = 1) (hb : d198467 q = 1) : d201072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d201072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16625, d201072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16626 q = 1) (hb : d198467 q = 1) : d201073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d201073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d201073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16627 q = 1) (hb : d198467 q = 1) : d201074 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d201074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d201074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16629 q = 1) (hb : d198467 q = 1) : d201076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d201076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53460 q ha hb
    | true =>
      simp only [d16629, d201076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16630 q = 1) (hb : d198467 q = 1) : d201077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d201077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d201077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16631 q = 1) (hb : d198467 q = 1) : d201078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d201078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16631, d201078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16632 q = 1) (hb : d198467 q = 1) : d201079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d201079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d201079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16633 q = 1) (hb : d198467 q = 1) : d201080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d201080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d201080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16634 q = 1) (hb : d198467 q = 1) : d201081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16634, d201081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16634, d201081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53466 (p : Pattern) (ha : d16643 p = 1) (hb : d198467 p = 1) : d201090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16629 q = 1) (hb : d198467 q = 1) : d201076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d201076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53460 q ha hb
    | true =>
      simp only [d16629, d201076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16630 q = 1) (hb : d198467 q = 1) : d201077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d201077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d201077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16631 q = 1) (hb : d198467 q = 1) : d201078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d201078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16631, d201078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16632 q = 1) (hb : d198467 q = 1) : d201079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d201079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d201079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16633 q = 1) (hb : d198467 q = 1) : d201080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d201080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d201080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16643 q = 1) (hb : d198467 q = 1) : d201090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16643, d201090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16643, d201090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53467 (p : Pattern) (ha : d15042 p = 1) (hb : d198467 p = 1) : d201132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d198467 q = 1) : d201112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53445 q ha hb
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53445 q ha hb
    | true =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1392 q = 1) (hb : d198467 q = 1) : d201113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1392, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1122 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1393 q = 1) (hb : d198467 q = 1) : d201114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1393, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1394 q = 1) (hb : d198467 q = 1) : d201115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1394, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1400 q = 1) (hb : d198467 q = 1) : d201121 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d201121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1400, d201121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15023 q = 1) (hb : d198467 q = 1) : d15023 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15042 q = 1) (hb : d198467 q = 1) : d201132 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15042, d201132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15042, d201132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro53468 (p : Pattern) (ha : d16672 p = 1) (hb : d198467 p = 1) : d201128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d198467 q = 1) : d201107 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d201107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d201107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53452 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d198467 q = 1) : d200922 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53452 q ha hb
    | true =>
      simp only [d1110, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d198467 q = 1) : d201108 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d201108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d201108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d198467 q = 1) : d200923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d198467 q = 1) : d201109 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d201109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d201109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d198467 q = 1) : d201110 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d201110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d201110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d198467 q = 1) : d201112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53445 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53445 q ha hb
    | true =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d198467 q = 1) : d201113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1393 q = 1) (hb : d198467 q = 1) : d201114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1393, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1394 q = 1) (hb : d198467 q = 1) : d201115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1394, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1395 q = 1) (hb : d198467 q = 1) : d201127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d201127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1395, d201127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15004 q = 1) (hb : d198467 q = 1) : d201112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53450 q ha hb
  have h15 (q : Pattern) (ha : d9800 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53450 q ha hb
    | true =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15005 q = 1) (hb : d198467 q = 1) : d201113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15005, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9802 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15006 q = 1) (hb : d198467 q = 1) : d201114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15006, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15007 q = 1) (hb : d198467 q = 1) : d201115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15007, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15008 q = 1) (hb : d198467 q = 1) : d201121 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d201121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15008, d201121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d16672 q = 1) (hb : d198467 q = 1) : d201128 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16672, d201128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16672, d201128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro53469 (p : Pattern) (ha : d16698 p = 1) (hb : d198467 p = 1) : d201151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16693 q = 1) (hb : d198467 q = 1) : d201133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53468 q ha hb
    | true =>
      simp only [d16693, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53467 q ha hb
  have h2 (q : Pattern) (ha : d16694 q = 1) (hb : d198467 q = 1) : d201134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16695 q = 1) (hb : d198467 q = 1) : d201135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16696 q = 1) (hb : d198467 q = 1) : d201141 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d201141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16696, d201141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16697 q = 1) (hb : d198467 q = 1) : d201150 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, d201150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16697, d201150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16698 q = 1) (hb : d198467 q = 1) : d201151 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16698, d201151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16698, d201151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53470 (p : Pattern) (ha : d16765 p = 1) (hb : d198467 p = 1) : d201183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16699 q = 1) (hb : d198467 q = 1) : d201152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d201152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53469 q ha hb
    | true =>
      simp only [d16699, d201152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16700 q = 1) (hb : d198467 q = 1) : d201153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d201153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d201153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16762 q = 1) (hb : d198467 q = 1) : d201180 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16762, d201180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16762, d201180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16763 q = 1) (hb : d198467 q = 1) : d201181 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16763, d201181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16763, d201181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16764 q = 1) (hb : d198467 q = 1) : d201182 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16764, d201182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16764, d201182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16765 q = 1) (hb : d198467 q = 1) : d201183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16765, d201183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16765, d201183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53471 (p : Pattern) (ha : d16771 p = 1) (hb : d198467 p = 1) : d201189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16766 q = 1) (hb : d198467 q = 1) : d201184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16766, d201184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53470 q ha hb
    | true =>
      simp only [d16766, d201184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16767 q = 1) (hb : d198467 q = 1) : d201185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16767, d201185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16767, d201185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16768 q = 1) (hb : d198467 q = 1) : d201186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16768, d201186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16768, d201186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16769 q = 1) (hb : d198467 q = 1) : d201187 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16769, d201187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16769, d201187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16770 q = 1) (hb : d198467 q = 1) : d201188 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16770, d201188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16770, d201188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16771 q = 1) (hb : d198467 q = 1) : d201189 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16771, d201189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16771, d201189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53472 (p : Pattern) (ha : d16491 p = 1) (hb : d198467 p = 1) : d200987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53454 q ha hb
    | true =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d198467 q = 1) : d200959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d198467 q = 1) : d200960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d198467 q = 1) : d200986 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d200986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d200986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16491 q = 1) (hb : d198467 q = 1) : d200987 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16491, d200987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16491, d200987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53473 (p : Pattern) (ha : d16493 p = 1) (hb : d198467 p = 1) : d200989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d198467 q = 1) : d200963 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d198467 q = 1) : d200964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d198467 q = 1) : d200988 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d200988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d200988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16493 q = 1) (hb : d198467 q = 1) : d200989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16493, d200989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16493, d200989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53474 (p : Pattern) (ha : d16500 p = 1) (hb : d198467 p = 1) : d200996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53454 q ha hb
    | true =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d198467 q = 1) : d200959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d198467 q = 1) : d200994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d200994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d200994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d198467 q = 1) : d200995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d200995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d200995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16500 q = 1) (hb : d198467 q = 1) : d200996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16500, d200996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16500, d200996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53475 (p : Pattern) (ha : d16503 p = 1) (hb : d198467 p = 1) : d200999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d198467 q = 1) : d200963 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d198467 q = 1) : d200997 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d200997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d200997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d198467 q = 1) : d200998 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d200998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d200998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16503 q = 1) (hb : d198467 q = 1) : d200999 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16503, d200999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16503, d200999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53476 (p : Pattern) (ha : d1209 p = 1) (hb : d198467 p = 1) : d201003 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1201 q = 1) : d1201 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d823 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1202 q = 1) (hb : d152852 q = 1) : d10042 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1202, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1202, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1205 q = 1) : d1205 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d829 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1206 q = 1) (hb : d152852 q = 1) : d26185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1206, d152852, d26185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1206, d152852, d26185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1207 q = 1) (hb : d152852 q = 1) : d26186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1207, d26186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1207, d26186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1208 q = 1) (hb : d152852 q = 1) : d26187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1208, d26187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1208, d26187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1092 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1209 q = 1) (hb : d198467 q = 1) : d201003 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1209, d198467, d201003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1209, d198467, d201003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53477 (p : Pattern) (ha : d9752 p = 1) (hb : d198467 p = 1) : d200745 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d829 q = 1) : d829 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d538 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d830 q = 1) (hb : d152852 q = 1) : d25761 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1091 q = 1) (hb : d152852 q = 1) : d25762 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1091, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1091, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1092 q = 1) (hb : d152852 q = 1) : d25763 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1092, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1092, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9751 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9752 q = 1) (hb : d198467 q = 1) : d200745 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9752, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9752, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53478 (p : Pattern) (ha : d9762 p = 1) (hb : d198467 p = 1) : d21840 p = 1 := by
  have h0 (q : Pattern) (ha : d9761 q = 1) (hb : d152852 q = 1) : d9761 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9762 q = 1) (hb : d198467 q = 1) : d21840 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9762, d198467, d21840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9762, d198467, d21840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro53479 (p : Pattern) (ha : d16511 p = 1) (hb : d198467 p = 1) : d201010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d198467 q = 1) : d201004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53476 q ha hb
    | true =>
      simp only [d1210, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1211 q = 1) (hb : d198467 q = 1) : d201005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1211, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1212 q = 1) (hb : d198467 q = 1) : d201006 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d201006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d201006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d198467 q = 1) : d201007 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d201007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1213, d201007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9753 q = 1) (hb : d198467 q = 1) : d200746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53477 q ha hb
    | true =>
      simp only [d9753, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9755 q = 1) (hb : d198467 q = 1) : d200747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9755, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16507 q = 1) (hb : d198467 q = 1) : d200748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16507, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16507, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16508 q = 1) (hb : d198467 q = 1) : d200749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16508, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16508, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16509 q = 1) (hb : d198467 q = 1) : d201008 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16509, d201008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16509, d201008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9763 q = 1) (hb : d198467 q = 1) : d21841 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53478 q ha hb
    | true =>
      simp only [d9763, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9765 q = 1) (hb : d198467 q = 1) : d21842 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9765, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14836 q = 1) (hb : d198467 q = 1) : d21843 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14836, d21843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14836, d21843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14837 q = 1) (hb : d198467 q = 1) : d21844 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14837, d21844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14837, d21844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9778 q = 1) (hb : d198467 q = 1) : d200928 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53448 q ha hb
    | true =>
      simp only [d9778, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9780 q = 1) (hb : d198467 q = 1) : d200929 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9780, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14758 q = 1) (hb : d198467 q = 1) : d200930 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14758, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14759 q = 1) (hb : d198467 q = 1) : d200931 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14759, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16510 q = 1) (hb : d198467 q = 1) : d201009 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16510, d201009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16510, d201009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16511 q = 1) (hb : d198467 q = 1) : d201010 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16511, d201010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16511, d201010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro53480 (p : Pattern) (ha : d9813 p = 1) (hb : d198467 p = 1) : d200927 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1089 q = 1) : d1089 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9810 q = 1) (hb : d152852 q = 1) : d26079 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9810, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9810, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9811 q = 1) (hb : d152852 q = 1) : d26098 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9811, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9811, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9812 q = 1) (hb : d152852 q = 1) : d26099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9812, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9812, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9776 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9813 q = 1) (hb : d198467 q = 1) : d200927 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9813, d198467, d200927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9813, d198467, d200927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro53481 (p : Pattern) (ha : d16516 p = 1) (hb : d198467 p = 1) : d201014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9814 q = 1) (hb : d198467 q = 1) : d200928 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53480 q ha hb
    | true =>
      simp only [d9814, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9816 q = 1) (hb : d198467 q = 1) : d200929 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9816, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13022 q = 1) (hb : d198467 q = 1) : d200930 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13022, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13022, d200930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13023 q = 1) (hb : d198467 q = 1) : d200931 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13023, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13023, d200931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9800 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53450 q ha hb
    | true =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9802 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14763 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14764 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14764, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16515 q = 1) (hb : d198467 q = 1) : d200937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16515, d200937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16515, d200937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14765 q = 1) (hb : d198467 q = 1) : d200940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14765, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16516 q = 1) (hb : d198467 q = 1) : d201014 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16516, d201014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16516, d201014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53482 (p : Pattern) (ha : d16522 p = 1) (hb : d198467 p = 1) : d201020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16512 q = 1) (hb : d198467 q = 1) : d201011 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16512, d201011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53479 q ha hb
    | true =>
      simp only [d16512, d201011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53451 q ha hb
  have h2 (q : Pattern) (ha : d16513 q = 1) (hb : d198467 q = 1) : d201012 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16513, d201012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16513, d201012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16514 q = 1) (hb : d198467 q = 1) : d201013 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16514, d201013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16514, d201013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16517 q = 1) (hb : d198467 q = 1) : d201015 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16517, d201015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53451 q ha hb
    | true =>
      simp only [d16517, d201015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53481 q ha hb
  have h5 (q : Pattern) (ha : d16518 q = 1) (hb : d198467 q = 1) : d201016 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16518, d201016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16518, d201016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16519 q = 1) (hb : d198467 q = 1) : d201017 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16519, d201017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16519, d201017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16520 q = 1) (hb : d198467 q = 1) : d201018 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16520, d201018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16520, d201018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16444 q = 1) (hb : d198467 q = 1) : d200942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d200942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53451 q ha hb
    | true =>
      simp only [d16444, d200942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53453 q ha hb
  have h9 (q : Pattern) (ha : d16445 q = 1) (hb : d198467 q = 1) : d200943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d200943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d200943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16446 q = 1) (hb : d198467 q = 1) : d200944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d200944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d200944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16447 q = 1) (hb : d198467 q = 1) : d200946 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53453 q ha hb
    | true =>
      simp only [d16447, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53444 q ha hb
  have h12 (q : Pattern) (ha : d16448 q = 1) (hb : d198467 q = 1) : d200947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16449 q = 1) (hb : d198467 q = 1) : d200948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16450 q = 1) (hb : d198467 q = 1) : d200949 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d200949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16450, d200949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16521 q = 1) (hb : d198467 q = 1) : d201019 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16521, d201019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16521, d201019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16522 q = 1) (hb : d198467 q = 1) : d201020 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16522, d201020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16522, d201020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro53483 (p : Pattern) (ha : d16533 p = 1) (hb : d198467 p = 1) : d201026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d198467 q = 1) : d201021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d201021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53482 q ha hb
    | true =>
      simp only [d16523, d201021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d198467 q = 1) : d201022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d201022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d201022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53462 q ha hb
    | true =>
      simp only [d16528, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d198467 q = 1) : d201023 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d201023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d201023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d198467 q = 1) : d201024 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d201024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d201024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d198467 q = 1) : d201025 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d201025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d201025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16533 q = 1) (hb : d198467 q = 1) : d201026 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16533, d201026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16533, d201026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53484 (p : Pattern) (ha : d12961 p = 1) (hb : d198467 p = 1) : d201029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53445 q ha hb
    | true =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d198467 q = 1) : d200935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d200935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d198467 q = 1) : d200936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d200936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d198467 q = 1) : d200940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d200940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12961 q = 1) (hb : d198467 q = 1) : d201029 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, d201029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12961, d201029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53485 (p : Pattern) (ha : d16579 p = 1) (hb : d198467 p = 1) : d201035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d198467 q = 1) : d200942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d200942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53451 q ha hb
    | true =>
      simp only [d16444, d200942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53453 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d198467 q = 1) : d200943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d200943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d200943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d198467 q = 1) : d200944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d200944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d200944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d198467 q = 1) : d200946 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53453 q ha hb
    | true =>
      simp only [d16447, d200946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53444 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d198467 q = 1) : d200947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d200947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d198467 q = 1) : d200948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d200948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d198467 q = 1) : d200949 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d200949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d200949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16574 q = 1) (hb : d198467 q = 1) : d201030 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16574, d201030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53453 q ha hb
    | true =>
      simp only [d16574, d201030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53484 q ha hb
  have h9 (q : Pattern) (ha : d16575 q = 1) (hb : d198467 q = 1) : d201031 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16575, d201031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16575, d201031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16576 q = 1) (hb : d198467 q = 1) : d201032 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16576, d201032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16576, d201032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16577 q = 1) (hb : d198467 q = 1) : d201033 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16577, d201033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16577, d201033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16578 q = 1) (hb : d198467 q = 1) : d201034 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16578, d201034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16578, d201034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16579 q = 1) (hb : d198467 q = 1) : d201035 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16579, d201035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16579, d201035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53486 (p : Pattern) (ha : d16585 p = 1) (hb : d198467 p = 1) : d201041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d198467 q = 1) : d201036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d201036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53485 q ha hb
    | true =>
      simp only [d16580, d201036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d198467 q = 1) : d201037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d201037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d201037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d198467 q = 1) : d201038 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d201038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d201038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d198467 q = 1) : d201039 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d201039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d201039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d198467 q = 1) : d201040 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d201040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d201040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16585 q = 1) (hb : d198467 q = 1) : d201041 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16585, d201041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16585, d201041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53487 (p : Pattern) (ha : d128315 p = 1) (hb : d198467 p = 1) : d201047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d198467 q = 1) : d200990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d200990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53472 q ha hb
    | true =>
      simp only [d16494, d200990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53473 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d198467 q = 1) : d200991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d200991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d200991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d198467 q = 1) : d200992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d200992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d200992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d198467 q = 1) : d200993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d200993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d200993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d198467 q = 1) : d201000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d201000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53474 q ha hb
    | true =>
      simp only [d16504, d201000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53475 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d198467 q = 1) : d201001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d201001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d201001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d198467 q = 1) : d201002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d201002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d201002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d198467 q = 1) : d201027 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d201027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53483 q ha hb
    | true =>
      simp only [d16538, d201027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53463 q ha hb
  have h9 (q : Pattern) (ha : d128311 q = 1) (hb : d198467 q = 1) : d201028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d201028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128311, d201028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d198467 q = 1) : d201042 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d201042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53486 q ha hb
    | true =>
      simp only [d16586, d201042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d198467 q = 1) : d201043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d201043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d201043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128312 q = 1) (hb : d198467 q = 1) : d201044 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d201044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d201044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128313 q = 1) (hb : d198467 q = 1) : d201045 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d201045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128313, d201045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128314 q = 1) (hb : d198467 q = 1) : d201046 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d201046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128314, d201046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128315 q = 1) (hb : d198467 q = 1) : d201047 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128315, d201047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128315, d201047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53488 (p : Pattern) (ha : d16592 p = 1) (hb : d198467 p = 1) : d201048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53454 q ha hb
    | true =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d198467 q = 1) : d200959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d198467 q = 1) : d200960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d198467 q = 1) : d200986 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d200986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d200986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16592 q = 1) (hb : d198467 q = 1) : d201048 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16592, d201048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16592, d201048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53489 (p : Pattern) (ha : d16593 p = 1) (hb : d198467 p = 1) : d201049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d198467 q = 1) : d200963 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d198467 q = 1) : d200964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d200964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d198467 q = 1) : d200988 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d200988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d200988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16593 q = 1) (hb : d198467 q = 1) : d201049 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16593, d201049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16593, d201049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53490 (p : Pattern) (ha : d16598 p = 1) (hb : d198467 p = 1) : d201054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53454 q ha hb
    | true =>
      simp only [d16457, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d198467 q = 1) : d200959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d198467 q = 1) : d200994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d200994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d200994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d198467 q = 1) : d200995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d200995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d200995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16598 q = 1) (hb : d198467 q = 1) : d201054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16598, d201054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16598, d201054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53491 (p : Pattern) (ha : d16599 p = 1) (hb : d198467 p = 1) : d201055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d198467 q = 1) : d200963 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d200963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d198467 q = 1) : d200997 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d200997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d200997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d198467 q = 1) : d200998 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d200998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d200998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16599 q = 1) (hb : d198467 q = 1) : d201055 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16599, d201055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16599, d201055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53492 (p : Pattern) (ha : d16603 p = 1) (hb : d198467 p = 1) : d201059 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d198467 q = 1) : d201021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d201021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53482 q ha hb
    | true =>
      simp only [d16523, d201021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d198467 q = 1) : d201022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d201022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d201022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53462 q ha hb
    | true =>
      simp only [d16528, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d198467 q = 1) : d201023 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d201023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d201023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d198467 q = 1) : d201024 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d201024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d201024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d198467 q = 1) : d201025 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d201025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d201025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16603 q = 1) (hb : d198467 q = 1) : d201059 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16603, d201059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16603, d201059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53493 (p : Pattern) (ha : d16604 p = 1) (hb : d198467 p = 1) : d200975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d198467 q = 1) : d200953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53462 q ha hb
    | true =>
      simp only [d16528, d200953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d198467 q = 1) : d200954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d200954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d198467 q = 1) : d200957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53455 q ha hb
    | true =>
      simp only [d16461, d200957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d198467 q = 1) : d200958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d200958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d198467 q = 1) : d200959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d200959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d198467 q = 1) : d200960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d200960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d198467 q = 1) : d200961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d200961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16604 q = 1) (hb : d198467 q = 1) : d200975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16604, d200975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16604, d200975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53494 (p : Pattern) (ha : d16610 p = 1) (hb : d198467 p = 1) : d201062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d198467 q = 1) : d201036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d201036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53485 q ha hb
    | true =>
      simp only [d16580, d201036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d198467 q = 1) : d201037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d201037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d201037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d198467 q = 1) : d201038 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d201038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d201038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d198467 q = 1) : d201039 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d201039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d201039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d198467 q = 1) : d201040 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d201040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d201040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16610 q = 1) (hb : d198467 q = 1) : d201062 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16610, d201062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16610, d201062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53495 (p : Pattern) (ha : d128320 p = 1) (hb : d198467 p = 1) : d201068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d198467 q = 1) : d200990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d200990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53472 q ha hb
    | true =>
      simp only [d16494, d200990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53473 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d198467 q = 1) : d200991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d200991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d200991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d198467 q = 1) : d200992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d200992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d200992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d198467 q = 1) : d200993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d200993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d200993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d198467 q = 1) : d201000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d201000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53474 q ha hb
    | true =>
      simp only [d16504, d201000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53475 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d198467 q = 1) : d201001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d201001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d201001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d198467 q = 1) : d201002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d201002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d201002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d198467 q = 1) : d201027 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d201027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53483 q ha hb
    | true =>
      simp only [d16538, d201027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53463 q ha hb
  have h9 (q : Pattern) (ha : d128311 q = 1) (hb : d198467 q = 1) : d201028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d201028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128311, d201028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d198467 q = 1) : d201042 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d201042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53486 q ha hb
    | true =>
      simp only [d16586, d201042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d198467 q = 1) : d201043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d201043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d201043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128312 q = 1) (hb : d198467 q = 1) : d201044 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d201044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d201044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128313 q = 1) (hb : d198467 q = 1) : d201045 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d201045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128313, d201045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128314 q = 1) (hb : d198467 q = 1) : d201046 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d201046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128314, d201046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16594 q = 1) (hb : d198467 q = 1) : d201050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16594, d201050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53488 q ha hb
    | true =>
      simp only [d16594, d201050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53489 q ha hb
  have h16 (q : Pattern) (ha : d16595 q = 1) (hb : d198467 q = 1) : d201051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16595, d201051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16595, d201051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16596 q = 1) (hb : d198467 q = 1) : d201052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16596, d201052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16596, d201052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16597 q = 1) (hb : d198467 q = 1) : d201053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16597, d201053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16597, d201053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16600 q = 1) (hb : d198467 q = 1) : d201056 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16600, d201056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53490 q ha hb
    | true =>
      simp only [d16600, d201056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53491 q ha hb
  have h20 (q : Pattern) (ha : d16601 q = 1) (hb : d198467 q = 1) : d201057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16601, d201057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16601, d201057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16602 q = 1) (hb : d198467 q = 1) : d201058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16602, d201058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16602, d201058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16605 q = 1) (hb : d198467 q = 1) : d201060 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d201060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53492 q ha hb
    | true =>
      simp only [d16605, d201060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53493 q ha hb
  have h23 (q : Pattern) (ha : d128316 q = 1) (hb : d198467 q = 1) : d201061 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d201061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128316, d201061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16611 q = 1) (hb : d198467 q = 1) : d201063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d201063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53494 q ha hb
    | true =>
      simp only [d16611, d201063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16612 q = 1) (hb : d198467 q = 1) : d201064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d201064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16612, d201064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128317 q = 1) (hb : d198467 q = 1) : d201065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d201065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128317, d201065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128318 q = 1) (hb : d198467 q = 1) : d201066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128318, d201066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128318, d201066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128319 q = 1) (hb : d198467 q = 1) : d201067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128319, d201067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128319, d201067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128320 q = 1) (hb : d198467 q = 1) : d201068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128320, d201068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128320, d201068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro53496 (p : Pattern) (ha : d128327 p = 1) (hb : d198467 p = 1) : d201088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16605 q = 1) (hb : d198467 q = 1) : d201060 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d201060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53492 q ha hb
    | true =>
      simp only [d16605, d201060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53493 q ha hb
  have h2 (q : Pattern) (ha : d128316 q = 1) (hb : d198467 q = 1) : d201061 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d201061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128316, d201061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16611 q = 1) (hb : d198467 q = 1) : d201063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d201063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53494 q ha hb
    | true =>
      simp only [d16611, d201063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16612 q = 1) (hb : d198467 q = 1) : d201064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d201064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16612, d201064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128317 q = 1) (hb : d198467 q = 1) : d201065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d201065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128317, d201065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128325 q = 1) (hb : d198467 q = 1) : d201086 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128325, d201086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128325, d201086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128326 q = 1) (hb : d198467 q = 1) : d201087 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128326, d201087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128326, d201087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128327 q = 1) (hb : d198467 q = 1) : d201088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128327, d201088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128327, d201088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53497 (p : Pattern) (ha : d15024 p = 1) (hb : d198467 p = 1) : d201132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6350 q = 1) (hb : d198467 q = 1) : d201112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6350, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53443 q ha hb
  have h2 (q : Pattern) (ha : d5018 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53443 q ha hb
    | true =>
      simp only [d5018, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6351 q = 1) (hb : d198467 q = 1) : d201113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6351, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5019 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5019, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6352 q = 1) (hb : d198467 q = 1) : d201114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6352, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6352, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6353 q = 1) (hb : d198467 q = 1) : d201115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6353, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6353, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6354 q = 1) (hb : d198467 q = 1) : d201121 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d201121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6354, d201121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15023 q = 1) (hb : d198467 q = 1) : d15023 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15024 q = 1) (hb : d198467 q = 1) : d201132 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15024, d201132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15024, d201132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro53498 (p : Pattern) (ha : d16655 p = 1) (hb : d198467 p = 1) : d201106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d198467 q = 1) : d201096 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d201096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d201096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53476 q ha hb
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d198467 q = 1) : d201004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53476 q ha hb
    | true =>
      simp only [d1210, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1377 q = 1) (hb : d198467 q = 1) : d201097 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d201097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1377, d201097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1211 q = 1) (hb : d198467 q = 1) : d201005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1378 q = 1) (hb : d198467 q = 1) : d201098 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d201098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1378, d201098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1379 q = 1) (hb : d198467 q = 1) : d201099 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d201099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1379, d201099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16649 q = 1) (hb : d198467 q = 1) : d200834 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d200834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16649, d200834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53477 q ha hb
  have h8 (q : Pattern) (ha : d9753 q = 1) (hb : d198467 q = 1) : d200746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53477 q ha hb
    | true =>
      simp only [d9753, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16650 q = 1) (hb : d198467 q = 1) : d200835 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16650, d200835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16650, d200835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9755 q = 1) (hb : d198467 q = 1) : d200747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9755, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16651 q = 1) (hb : d198467 q = 1) : d200836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16651, d200836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16651, d200836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16652 q = 1) (hb : d198467 q = 1) : d200837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16652, d200837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16652, d200837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16653 q = 1) (hb : d198467 q = 1) : d201100 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16653, d201100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16653, d201100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14987 q = 1) (hb : d198467 q = 1) : d22033 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, d22033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14987, d22033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53478 q ha hb
  have h15 (q : Pattern) (ha : d9763 q = 1) (hb : d198467 q = 1) : d21841 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53478 q ha hb
    | true =>
      simp only [d9763, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14988 q = 1) (hb : d198467 q = 1) : d22034 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14988, d22034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14988, d22034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9765 q = 1) (hb : d198467 q = 1) : d21842 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9765, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14989 q = 1) (hb : d198467 q = 1) : d22035 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14989, d22035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14989, d22035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14990 q = 1) (hb : d198467 q = 1) : d22036 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14990, d22036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d14990, d22036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d14994 q = 1) (hb : d198467 q = 1) : d201101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d201101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d201101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53448 q ha hb
  have h21 (q : Pattern) (ha : d9778 q = 1) (hb : d198467 q = 1) : d200928 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53448 q ha hb
    | true =>
      simp only [d9778, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14995 q = 1) (hb : d198467 q = 1) : d201102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d201102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14995, d201102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9780 q = 1) (hb : d198467 q = 1) : d200929 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9780, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14996 q = 1) (hb : d198467 q = 1) : d201103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d201103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d14996, d201103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d14997 q = 1) (hb : d198467 q = 1) : d201104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d201104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14997, d201104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16654 q = 1) (hb : d198467 q = 1) : d201105 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16654, d201105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16654, d201105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16655 q = 1) (hb : d198467 q = 1) : d201106 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16655, d201106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16655, d201106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro53499 (p : Pattern) (ha : d16662 p = 1) (hb : d198467 p = 1) : d201117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d198467 q = 1) : d200834 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d200834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d200834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53447 q ha hb
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d198467 q = 1) : d200746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53447 q ha hb
    | true =>
      simp only [d1100, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1381 q = 1) (hb : d198467 q = 1) : d200835 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d200835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1381, d200835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1101 q = 1) (hb : d198467 q = 1) : d200747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1382 q = 1) (hb : d198467 q = 1) : d200836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d200836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1382, d200836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1383 q = 1) (hb : d198467 q = 1) : d200837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d200837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1383, d200837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16656 q = 1) (hb : d198467 q = 1) : d201107 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d201107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16656, d201107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53449 q ha hb
  have h8 (q : Pattern) (ha : d9789 q = 1) (hb : d198467 q = 1) : d200922 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53449 q ha hb
    | true =>
      simp only [d9789, d200922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16657 q = 1) (hb : d198467 q = 1) : d201108 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16657, d201108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16657, d201108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9791 q = 1) (hb : d198467 q = 1) : d200923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9791, d200923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16658 q = 1) (hb : d198467 q = 1) : d201109 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16658, d201109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16658, d201109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16659 q = 1) (hb : d198467 q = 1) : d201110 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16659, d201110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16659, d201110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16660 q = 1) (hb : d198467 q = 1) : d201111 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16660, d201111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16660, d201111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14994 q = 1) (hb : d198467 q = 1) : d201101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d201101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d201101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53448 q ha hb
  have h15 (q : Pattern) (ha : d9778 q = 1) (hb : d198467 q = 1) : d200928 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53448 q ha hb
    | true =>
      simp only [d9778, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14995 q = 1) (hb : d198467 q = 1) : d201102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d201102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14995, d201102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9780 q = 1) (hb : d198467 q = 1) : d200929 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9780, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14996 q = 1) (hb : d198467 q = 1) : d201103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d201103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14996, d201103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14997 q = 1) (hb : d198467 q = 1) : d201104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d201104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d14997, d201104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15004 q = 1) (hb : d198467 q = 1) : d201112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53450 q ha hb
  have h21 (q : Pattern) (ha : d9800 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53450 q ha hb
    | true =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15005 q = 1) (hb : d198467 q = 1) : d201113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15005, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9802 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d15006 q = 1) (hb : d198467 q = 1) : d201114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d15006, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d15007 q = 1) (hb : d198467 q = 1) : d201115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15007, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16661 q = 1) (hb : d198467 q = 1) : d201116 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16661, d201116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16661, d201116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16662 q = 1) (hb : d198467 q = 1) : d201117 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16662, d201117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16662, d201117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
end NetHack.Soko22Hazard87
