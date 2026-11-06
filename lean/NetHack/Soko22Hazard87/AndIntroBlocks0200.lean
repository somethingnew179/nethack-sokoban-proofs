import NetHack.Soko22Hazard87.AndIntroBlocks0199
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro50000 (p : Pattern) (ha : d22452 p = 1) (hb : d146837 p = 1) : d149356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22341 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49978 q ha hb
    | true =>
      simp only [d22341, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22342 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22347 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22347, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22347, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22348 q = 1) (hb : d146837 q = 1) : d149341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22348, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22348, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22349 q = 1) (hb : d146837 q = 1) : d149342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22349, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22349, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22452 q = 1) (hb : d146837 q = 1) : d149356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22452, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22452, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50001 (p : Pattern) (ha : d22458 p = 1) (hb : d146837 p = 1) : d149423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22428 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22428, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49992 q ha hb
    | true =>
      simp only [d22428, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22429 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22429, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22429, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22430 q = 1) (hb : d146837 q = 1) : d149399 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22430, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22430, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22431 q = 1) (hb : d146837 q = 1) : d149400 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22431, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22431, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22432 q = 1) (hb : d146837 q = 1) : d149401 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22432, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22432, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22458 q = 1) (hb : d146837 q = 1) : d149423 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22458, d149423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22458, d149423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50002 (p : Pattern) (ha : d146837 p = 1) (hb : d150206 p = 1) : d149429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22299 q = 1) (hb : d146837 q = 1) : d149371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22299, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49986 q ha hb
    | true =>
      simp only [d22299, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49987 q ha hb
  have h2 (q : Pattern) (ha : d22300 q = 1) (hb : d146837 q = 1) : d149372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22300, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22300, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22301 q = 1) (hb : d146837 q = 1) : d149373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22301, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22301, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22302 q = 1) (hb : d146837 q = 1) : d149374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22302, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22302, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22309 q = 1) (hb : d146837 q = 1) : d149381 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22309, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49988 q ha hb
    | true =>
      simp only [d22309, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49989 q ha hb
  have h6 (q : Pattern) (ha : d22310 q = 1) (hb : d146837 q = 1) : d149382 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22310, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22310, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22311 q = 1) (hb : d146837 q = 1) : d149383 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22311, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22311, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22351 q = 1) (hb : d146837 q = 1) : d149397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22351, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49991 q ha hb
    | true =>
      simp only [d22351, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49979 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150197 q = 1) : d149398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150197, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22434 q = 1) (hb : d146837 q = 1) : d149403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22434, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49993 q ha hb
    | true =>
      simp only [d22434, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22435 q = 1) (hb : d146837 q = 1) : d149404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22435, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22435, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150198 q = 1) : d149405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150198, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150199 q = 1) : d149406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150199, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150200 q = 1) : d149407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150200, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22442 q = 1) (hb : d146837 q = 1) : d149411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22442, d149411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49995 q ha hb
    | true =>
      simp only [d22442, d149411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49996 q ha hb
  have h16 (q : Pattern) (ha : d22443 q = 1) (hb : d146837 q = 1) : d149412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22443, d149412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22443, d149412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22444 q = 1) (hb : d146837 q = 1) : d149413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22444, d149413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22444, d149413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22445 q = 1) (hb : d146837 q = 1) : d149414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22445, d149414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22445, d149414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22448 q = 1) (hb : d146837 q = 1) : d149417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22448, d149417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49997 q ha hb
    | true =>
      simp only [d22448, d149417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49998 q ha hb
  have h20 (q : Pattern) (ha : d22449 q = 1) (hb : d146837 q = 1) : d149418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22449, d149418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22449, d149418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d22450 q = 1) (hb : d146837 q = 1) : d149419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22450, d149419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d22450, d149419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d22453 q = 1) (hb : d146837 q = 1) : d149421 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22453, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49999 q ha hb
    | true =>
      simp only [d22453, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50000 q ha hb
  have h23 (q : Pattern) (ha : d146837 q = 1) (hb : d150202 q = 1) : d149422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150202, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d22459 q = 1) (hb : d146837 q = 1) : d149424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22459, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50001 q ha hb
    | true =>
      simp only [d22459, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d22460 q = 1) (hb : d146837 q = 1) : d149425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22460, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d22460, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d146837 q = 1) (hb : d150203 q = 1) : d149426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150203, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d146837 q = 1) (hb : d150204 q = 1) : d149427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150204, d149427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150204, d149427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d146837 q = 1) (hb : d150205 q = 1) : d149428 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150205, d149428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150205, d149428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146837 q = 1) (hb : d150206 q = 1) : d149429 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150206, d149429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150206, d149429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro50003 (p : Pattern) (ha : d146837 p = 1) (hb : d150213 p = 1) : d149449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22453 q = 1) (hb : d146837 q = 1) : d149421 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22453, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49999 q ha hb
    | true =>
      simp only [d22453, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50000 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150202 q = 1) : d149422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150202, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22459 q = 1) (hb : d146837 q = 1) : d149424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22459, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50001 q ha hb
    | true =>
      simp only [d22459, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22460 q = 1) (hb : d146837 q = 1) : d149425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22460, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22460, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150203 q = 1) : d149426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150203, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150211 q = 1) : d149447 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150211, d149447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150211, d149447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150212 q = 1) : d149448 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150212, d149448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150212, d149448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150213 q = 1) : d149449 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150213, d149449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150213, d149449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50004 (p : Pattern) (ha : d22549 p = 1) (hb : d146837 p = 1) : d149472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22514 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22515 q = 1) (hb : d146837 q = 1) : d149458 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22515, d146837, d149458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45944 q ha hb
    | true =>
      simp only [d22515, d146837, d149458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22516 q = 1) (hb : d146837 q = 1) : d149459 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22516, d149459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22516, d149459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22517 q = 1) (hb : d146837 q = 1) : d149460 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22517, d149460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22517, d149460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22524 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22525 q = 1) (hb : d146837 q = 1) : d149462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22525, d146837, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45945 q ha hb
    | true =>
      simp only [d22525, d146837, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22526 q = 1) (hb : d146837 q = 1) : d149463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22526, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22526, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22527 q = 1) (hb : d146837 q = 1) : d149464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22527, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22527, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22528 q = 1) (hb : d146837 q = 1) : d149465 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22528, d149465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22528, d149465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22534 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22535 q = 1) (hb : d146837 q = 1) : d149462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d146837, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45945 q ha hb
    | true =>
      simp only [d22535, d146837, d149462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22536 q = 1) (hb : d146837 q = 1) : d149463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d149463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22537 q = 1) (hb : d146837 q = 1) : d149464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d149464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22543 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22544 q = 1) (hb : d146837 q = 1) : d149467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
    | true =>
      simp only [d22544, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d22545 q = 1) (hb : d146837 q = 1) : d149468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22546 q = 1) (hb : d146837 q = 1) : d149469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d22547 q = 1) (hb : d146837 q = 1) : d149470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22547, d149470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22548 q = 1) (hb : d146837 q = 1) : d149471 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22548, d149471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22548, d149471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d22549 q = 1) (hb : d146837 q = 1) : d149472 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22549, d149472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22549, d149472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro50005 (p : Pattern) (ha : d22554 p = 1) (hb : d146837 p = 1) : d149477 p = 1 := by
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
  have h10 (q : Pattern) (ha : d22552 q = 1) (hb : d146837 q = 1) : d149475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22552, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22552, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22553 q = 1) (hb : d146837 q = 1) : d149476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22553, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22553, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22554 q = 1) (hb : d146837 q = 1) : d149477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22554, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22554, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro50006 (p : Pattern) (ha : d22560 p = 1) (hb : d146837 p = 1) : d149483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22550 q = 1) (hb : d146837 q = 1) : d149473 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22550, d149473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50004 q ha hb
    | true =>
      simp only [d22550, d149473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22551 q = 1) (hb : d146837 q = 1) : d149474 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22551, d149474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22551, d149474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22555 q = 1) (hb : d146837 q = 1) : d149478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22555, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50005 q ha hb
    | true =>
      simp only [d22555, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22556 q = 1) (hb : d146837 q = 1) : d149479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22556, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22556, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22557 q = 1) (hb : d146837 q = 1) : d149480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22557, d149480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22557, d149480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22558 q = 1) (hb : d146837 q = 1) : d149481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22558, d149481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22558, d149481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22559 q = 1) (hb : d146837 q = 1) : d149482 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22559, d149482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22559, d149482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22560 q = 1) (hb : d146837 q = 1) : d149483 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22560, d149483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22560, d149483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50007 (p : Pattern) (ha : d22574 p = 1) (hb : d146837 p = 1) : d149491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22555 q = 1) (hb : d146837 q = 1) : d149478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22555, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50005 q ha hb
    | true =>
      simp only [d22555, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22556 q = 1) (hb : d146837 q = 1) : d149479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22556, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22556, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d22571 q = 1) (hb : d146837 q = 1) : d149488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22571, d149488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22571, d149488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22572 q = 1) (hb : d146837 q = 1) : d149489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22572, d149489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22572, d149489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22573 q = 1) (hb : d146837 q = 1) : d149490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22573, d149490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22573, d149490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22574 q = 1) (hb : d146837 q = 1) : d149491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22574, d149491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22574, d149491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50008 (p : Pattern) (ha : d22645 p = 1) (hb : d146837 p = 1) : d149477 p = 1 := by
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
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22639 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22640 q = 1) (hb : d146837 q = 1) : d149467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22640, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
    | true =>
      simp only [d22640, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22641 q = 1) (hb : d146837 q = 1) : d149468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22641, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22641, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22642 q = 1) (hb : d146837 q = 1) : d149469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22642, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22642, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22643 q = 1) (hb : d146837 q = 1) : d149475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22643, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22643, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22644 q = 1) (hb : d146837 q = 1) : d149476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22644, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22644, d149476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22645 q = 1) (hb : d146837 q = 1) : d149477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22645, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22645, d149477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro50009 (p : Pattern) (ha : d22651 p = 1) (hb : d146837 p = 1) : d149497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22646 q = 1) (hb : d146837 q = 1) : d149478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22646, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50008 q ha hb
    | true =>
      simp only [d22646, d149478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22647 q = 1) (hb : d146837 q = 1) : d149479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22647, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22647, d149479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22648 q = 1) (hb : d146837 q = 1) : d149494 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22648, d149494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22648, d149494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22649 q = 1) (hb : d146837 q = 1) : d149495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22649, d149495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22649, d149495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22650 q = 1) (hb : d146837 q = 1) : d149496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22650, d149496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22650, d149496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22651 q = 1) (hb : d146837 q = 1) : d149497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22651, d149497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22651, d149497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50010 (p : Pattern) (ha : d146837 p = 1) (hb : d150223 p = 1) : d149503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22575 q = 1) (hb : d146837 q = 1) : d149492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22575, d149492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50006 q ha hb
    | true =>
      simp only [d22575, d149492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50007 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150219 q = 1) : d149493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150219, d149493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150219, d149493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22652 q = 1) (hb : d146837 q = 1) : d149498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22652, d149498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50009 q ha hb
    | true =>
      simp only [d22652, d149498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22653 q = 1) (hb : d146837 q = 1) : d149499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22653, d149499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22653, d149499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150220 q = 1) : d149500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150220, d149500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150220, d149500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150221 q = 1) : d149501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150221, d149501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150221, d149501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150222 q = 1) : d149502 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150222, d149502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150222, d149502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150223 q = 1) : d149503 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150223, d149503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150223, d149503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50011 (p : Pattern) (ha : d146837 p = 1) (hb : d150229 p = 1) : d149520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22282 q = 1) (hb : d146837 q = 1) : d149354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22282, d149354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22282, d149354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49974 q ha hb
  have h2 (q : Pattern) (ha : d22283 q = 1) (hb : d146837 q = 1) : d149355 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22283, d149355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22283, d149355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22292 q = 1) (hb : d146837 q = 1) : d149364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49974 q ha hb
    | true =>
      simp only [d22292, d149364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49977 q ha hb
  have h4 (q : Pattern) (ha : d22293 q = 1) (hb : d146837 q = 1) : d149365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22293, d149365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22294 q = 1) (hb : d146837 q = 1) : d149366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d22294, d149366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22294, d149366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150207 q = 1) : d149430 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150207, d149430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49994 q ha hb
    | true =>
      simp only [d150207, d149430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50002 q ha hb
  have h7 (q : Pattern) (ha : d22483 q = 1) (hb : d146837 q = 1) : d149443 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22483, d149443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49980 q ha hb
    | true =>
      simp only [d22483, d149443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49981 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150208 q = 1) : d149444 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150208, d149444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150208, d149444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150209 q = 1) : d149445 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150209, d149445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150209, d149445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d150210 q = 1) : d149446 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150210, d149446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150210, d149446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d150214 q = 1) : d149450 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150214, d149450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150214, d149450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50003 q ha hb
  have h12 (q : Pattern) (ha : d22492 q = 1) (hb : d146837 q = 1) : d149452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22492, d149452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22492, d149452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49982 q ha hb
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150215 q = 1) : d149453 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150215, d149453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150215, d149453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150216 q = 1) : d149454 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150216, d149454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150216, d149454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150217 q = 1) : d149455 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150217, d149455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150217, d149455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d150218 q = 1) : d149456 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150218, d149456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150218, d149456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146837 q = 1) (hb : d150224 q = 1) : d149504 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150224, d149504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150224, d149504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50010 q ha hb
  have h18 (q : Pattern) (ha : d22669 q = 1) (hb : d146837 q = 1) : d149515 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22669, d149515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22669, d149515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49985 q ha hb
  have h19 (q : Pattern) (ha : d146837 q = 1) (hb : d150225 q = 1) : d149516 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150225, d149516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150225, d149516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d146837 q = 1) (hb : d150226 q = 1) : d149517 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150226, d149517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150226, d149517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d146837 q = 1) (hb : d150227 q = 1) : d149518 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150227, d149518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150227, d149518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d146837 q = 1) (hb : d150228 q = 1) : d149519 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150228, d149519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150228, d149519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146837 q = 1) (hb : d150229 q = 1) : d149520 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150229, d149520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150229, d149520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro50012 (p : Pattern) (ha : d146837 p = 1) (hb : d150235 p = 1) : d149526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150230 q = 1) : d149521 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150230, d149521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150230, d149521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50011 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150231 q = 1) : d149522 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150231, d149522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150231, d149522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150232 q = 1) : d149523 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150232, d149523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150232, d149523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150233 q = 1) : d149524 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150233, d149524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150233, d149524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150234 q = 1) : d149525 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150234, d149525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150234, d149525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150235 q = 1) : d149526 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150235, d149526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150235, d149526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50013 (p : Pattern) (ha : d22716 p = 1) (hb : d146837 p = 1) : d149542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22694 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22695 q = 1) (hb : d146837 q = 1) : d149532 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d146837, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45957 q ha hb
    | true =>
      simp only [d22695, d146837, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22696 q = 1) (hb : d146837 q = 1) : d149533 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22697 q = 1) (hb : d146837 q = 1) : d149534 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22705 q = 1) (hb : d146837 q = 1) : d149536 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22705, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22706 q = 1) (hb : d146837 q = 1) : d149537 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22707 q = 1) (hb : d146837 q = 1) : d149538 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22708 q = 1) (hb : d146837 q = 1) : d149539 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22708, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22710 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22711 q = 1) (hb : d146837 q = 1) : d149536 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22711, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22711, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22712 q = 1) (hb : d146837 q = 1) : d149537 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22712, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22712, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22713 q = 1) (hb : d146837 q = 1) : d149538 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22713, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22713, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22714 q = 1) (hb : d146837 q = 1) : d149540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22714, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22714, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22715 q = 1) (hb : d146837 q = 1) : d149541 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22715, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22715, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22716 q = 1) (hb : d146837 q = 1) : d149542 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22716, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22716, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro50014 (p : Pattern) (ha : d22720 p = 1) (hb : d146837 p = 1) : d149546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22710 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22711 q = 1) (hb : d146837 q = 1) : d149536 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22711, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22711, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22712 q = 1) (hb : d146837 q = 1) : d149537 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22712, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22712, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22713 q = 1) (hb : d146837 q = 1) : d149538 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22713, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22713, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22714 q = 1) (hb : d146837 q = 1) : d149540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22714, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22714, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22719 q = 1) (hb : d146837 q = 1) : d149545 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22719, d149545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22719, d149545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22720 q = 1) (hb : d146837 q = 1) : d149546 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22720, d149546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22720, d149546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro50015 (p : Pattern) (ha : d22726 p = 1) (hb : d146837 p = 1) : d149552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50013 q ha hb
    | true =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146837 q = 1) : d149549 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d146837 q = 1) : d149550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22725 q = 1) (hb : d146837 q = 1) : d149551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22725, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22725, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22726 q = 1) (hb : d146837 q = 1) : d149552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22726, d149552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22726, d149552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50016 (p : Pattern) (ha : d22730 p = 1) (hb : d146837 p = 1) : d149556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146837 q = 1) : d149553 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d146837 q = 1) : d149554 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22729 q = 1) (hb : d146837 q = 1) : d149555 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22729, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22729, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22730 q = 1) (hb : d146837 q = 1) : d149556 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22730, d149556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22730, d149556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50017 (p : Pattern) (ha : d22736 p = 1) (hb : d146837 p = 1) : d149562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22731 q = 1) (hb : d146837 q = 1) : d149557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50015 q ha hb
    | true =>
      simp only [d22731, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50016 q ha hb
  have h2 (q : Pattern) (ha : d22732 q = 1) (hb : d146837 q = 1) : d149558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22732, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22733 q = 1) (hb : d146837 q = 1) : d149559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22733, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22734 q = 1) (hb : d146837 q = 1) : d149560 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22734, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22735 q = 1) (hb : d146837 q = 1) : d149561 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22736 q = 1) (hb : d146837 q = 1) : d149562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22736, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22736, d149562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50018 (p : Pattern) (ha : d22739 p = 1) (hb : d146837 p = 1) : d149565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50013 q ha hb
    | true =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146837 q = 1) : d149549 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d146837 q = 1) : d149550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22725 q = 1) (hb : d146837 q = 1) : d149551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22725, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22725, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22739 q = 1) (hb : d146837 q = 1) : d149565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22739, d149565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22739, d149565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50019 (p : Pattern) (ha : d22740 p = 1) (hb : d146837 p = 1) : d149566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146837 q = 1) : d149553 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d146837 q = 1) : d149554 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22729 q = 1) (hb : d146837 q = 1) : d149555 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22729, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22729, d149555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22740 q = 1) (hb : d146837 q = 1) : d149566 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22740, d149566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22740, d149566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50020 (p : Pattern) (ha : d22746 p = 1) (hb : d146837 p = 1) : d149572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22731 q = 1) (hb : d146837 q = 1) : d149557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50015 q ha hb
    | true =>
      simp only [d22731, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50016 q ha hb
  have h2 (q : Pattern) (ha : d22732 q = 1) (hb : d146837 q = 1) : d149558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22732, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22733 q = 1) (hb : d146837 q = 1) : d149559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22733, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22734 q = 1) (hb : d146837 q = 1) : d149560 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22734, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22735 q = 1) (hb : d146837 q = 1) : d149561 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22741 q = 1) (hb : d146837 q = 1) : d149567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50018 q ha hb
    | true =>
      simp only [d22741, d149567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50019 q ha hb
  have h7 (q : Pattern) (ha : d22742 q = 1) (hb : d146837 q = 1) : d149568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d149568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22743 q = 1) (hb : d146837 q = 1) : d149569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22743, d149569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22744 q = 1) (hb : d146837 q = 1) : d149570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d149570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22745 q = 1) (hb : d146837 q = 1) : d149571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d149571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22746 q = 1) (hb : d146837 q = 1) : d149572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22746, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22746, d149572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50021 (p : Pattern) (ha : d22783 p = 1) (hb : d146837 p = 1) : d149542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22694 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22695 q = 1) (hb : d146837 q = 1) : d149532 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d146837, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45957 q ha hb
    | true =>
      simp only [d22695, d146837, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22696 q = 1) (hb : d146837 q = 1) : d149533 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22697 q = 1) (hb : d146837 q = 1) : d149534 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22705 q = 1) (hb : d146837 q = 1) : d149536 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22705, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22706 q = 1) (hb : d146837 q = 1) : d149537 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22707 q = 1) (hb : d146837 q = 1) : d149538 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22708 q = 1) (hb : d146837 q = 1) : d149539 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22708, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22781 q = 1) (hb : d146837 q = 1) : d149540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22781, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22781, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22782 q = 1) (hb : d146837 q = 1) : d149541 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22782, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22782, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22783 q = 1) (hb : d146837 q = 1) : d149542 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22783, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22783, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro50022 (p : Pattern) (ha : d22793 p = 1) (hb : d146837 p = 1) : d149552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22784 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50021 q ha hb
    | true =>
      simp only [d22784, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22785 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22790 q = 1) (hb : d146837 q = 1) : d149549 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22790, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22790, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22791 q = 1) (hb : d146837 q = 1) : d149550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22791, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22791, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22792 q = 1) (hb : d146837 q = 1) : d149551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22792, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22792, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22793 q = 1) (hb : d146837 q = 1) : d149552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22793, d149552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22793, d149552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50023 (p : Pattern) (ha : d22909 p = 1) (hb : d146837 p = 1) : d149645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22899 q = 1) (hb : d146837 q = 1) : d149557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22899, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50022 q ha hb
    | true =>
      simp only [d22899, d149557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50016 q ha hb
  have h2 (q : Pattern) (ha : d22900 q = 1) (hb : d146837 q = 1) : d149558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22900, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22900, d149558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22901 q = 1) (hb : d146837 q = 1) : d149559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22901, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22901, d149559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22902 q = 1) (hb : d146837 q = 1) : d149560 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22902, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22902, d149560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22903 q = 1) (hb : d146837 q = 1) : d149561 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22903, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22903, d149561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22904 q = 1) (hb : d146837 q = 1) : d149640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22904, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50016 q ha hb
    | true =>
      simp only [d22904, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22905 q = 1) (hb : d146837 q = 1) : d149641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22905, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22905, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22906 q = 1) (hb : d146837 q = 1) : d149642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22906, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22906, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22907 q = 1) (hb : d146837 q = 1) : d149643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22907, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22907, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22908 q = 1) (hb : d146837 q = 1) : d149644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22908, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22908, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22909 q = 1) (hb : d146837 q = 1) : d149645 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22909, d149645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22909, d149645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50024 (p : Pattern) (ha : d22915 p = 1) (hb : d146837 p = 1) : d149651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22904 q = 1) (hb : d146837 q = 1) : d149640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22904, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50016 q ha hb
    | true =>
      simp only [d22904, d149640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22905 q = 1) (hb : d146837 q = 1) : d149641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22905, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22905, d149641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22906 q = 1) (hb : d146837 q = 1) : d149642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22906, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22906, d149642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22907 q = 1) (hb : d146837 q = 1) : d149643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22907, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22907, d149643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22908 q = 1) (hb : d146837 q = 1) : d149644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22908, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22908, d149644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22910 q = 1) (hb : d146837 q = 1) : d149646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22910, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50019 q ha hb
    | true =>
      simp only [d22910, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22911 q = 1) (hb : d146837 q = 1) : d149647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22911, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22911, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22912 q = 1) (hb : d146837 q = 1) : d149648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22912, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22912, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22913 q = 1) (hb : d146837 q = 1) : d149649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22913, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22913, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22914 q = 1) (hb : d146837 q = 1) : d149650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22914, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22914, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22915 q = 1) (hb : d146837 q = 1) : d149651 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22915, d149651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22915, d149651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50025 (p : Pattern) (ha : d22924 p = 1) (hb : d146837 p = 1) : d149660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22910 q = 1) (hb : d146837 q = 1) : d149646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22910, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50019 q ha hb
    | true =>
      simp only [d22910, d149646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22911 q = 1) (hb : d146837 q = 1) : d149647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22911, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22911, d149647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22912 q = 1) (hb : d146837 q = 1) : d149648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22912, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22912, d149648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22913 q = 1) (hb : d146837 q = 1) : d149649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22913, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22913, d149649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22914 q = 1) (hb : d146837 q = 1) : d149650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22914, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22914, d149650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22924 q = 1) (hb : d146837 q = 1) : d149660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22924, d149660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22924, d149660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50026 (p : Pattern) (ha : d22982 p = 1) (hb : d146837 p = 1) : d149694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22976 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22977 q = 1) (hb : d146837 q = 1) : d149676 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d146837, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45974 q ha hb
    | true =>
      simp only [d22977, d146837, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22978 q = 1) (hb : d146837 q = 1) : d149677 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22979 q = 1) (hb : d146837 q = 1) : d149678 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22980 q = 1) (hb : d146837 q = 1) : d149684 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22980, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22981 q = 1) (hb : d146837 q = 1) : d149693 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22981, d149693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22981, d149693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22982 q = 1) (hb : d146837 q = 1) : d149694 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22982, d149694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22982, d149694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro50027 (p : Pattern) (ha : d23068 p = 1) (hb : d146837 p = 1) : d149717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22983 q = 1) (hb : d146837 q = 1) : d149695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50026 q ha hb
    | true =>
      simp only [d22983, d149695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22984 q = 1) (hb : d146837 q = 1) : d149696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d149696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23065 q = 1) (hb : d146837 q = 1) : d149714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23065, d149714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23065, d149714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23066 q = 1) (hb : d146837 q = 1) : d149715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23066, d149715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23066, d149715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23067 q = 1) (hb : d146837 q = 1) : d149716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23067, d149716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23067, d149716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23068 q = 1) (hb : d146837 q = 1) : d149717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23068, d149717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23068, d149717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50028 (p : Pattern) (ha : d23074 p = 1) (hb : d146837 p = 1) : d149723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23069 q = 1) (hb : d146837 q = 1) : d149718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23069, d149718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50027 q ha hb
    | true =>
      simp only [d23069, d149718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23070 q = 1) (hb : d146837 q = 1) : d149719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23070, d149719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23070, d149719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23071 q = 1) (hb : d146837 q = 1) : d149720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23071, d149720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23071, d149720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23072 q = 1) (hb : d146837 q = 1) : d149721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23072, d149721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23072, d149721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23073 q = 1) (hb : d146837 q = 1) : d149722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23073, d149722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23073, d149722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23074 q = 1) (hb : d146837 q = 1) : d149723 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23074, d149723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23074, d149723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50029 (p : Pattern) (ha : d22751 p = 1) (hb : d146837 p = 1) : d149577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50013 q ha hb
    | true =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146837 q = 1) : d149549 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d146837 q = 1) : d149550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22750 q = 1) (hb : d146837 q = 1) : d149576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22750, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22750, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22751 q = 1) (hb : d146837 q = 1) : d149577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22751, d149577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22751, d149577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50030 (p : Pattern) (ha : d22753 p = 1) (hb : d146837 p = 1) : d149579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146837 q = 1) : d149553 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d146837 q = 1) : d149554 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22752 q = 1) (hb : d146837 q = 1) : d149578 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22752, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22752, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22753 q = 1) (hb : d146837 q = 1) : d149579 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22753, d149579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22753, d149579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50031 (p : Pattern) (ha : d22760 p = 1) (hb : d146837 p = 1) : d149586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50013 q ha hb
    | true =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146837 q = 1) : d149549 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22758 q = 1) (hb : d146837 q = 1) : d149584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22758, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22758, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22759 q = 1) (hb : d146837 q = 1) : d149585 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22759, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22759, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22760 q = 1) (hb : d146837 q = 1) : d149586 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22760, d149586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22760, d149586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50032 (p : Pattern) (ha : d22763 p = 1) (hb : d146837 p = 1) : d149589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146837 q = 1) : d149553 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22761 q = 1) (hb : d146837 q = 1) : d149587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22761, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22761, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22762 q = 1) (hb : d146837 q = 1) : d149588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22762, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22762, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22763 q = 1) (hb : d146837 q = 1) : d149589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22763, d149589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22763, d149589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50033 (p : Pattern) (ha : d22778 p = 1) (hb : d146837 p = 1) : d149599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22769 q = 1) (hb : d146837 q = 1) : d149594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22769, d146837, d149594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45983 q ha hb
    | true =>
      simp only [d22769, d146837, d149594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22770 q = 1) (hb : d146837 q = 1) : d149595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22770, d149595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22770, d149595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22771 q = 1) (hb : d146837 q = 1) : d149596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22771, d149596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22771, d149596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22772 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22773 q = 1) (hb : d146837 q = 1) : d149532 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22773, d146837, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45957 q ha hb
    | true =>
      simp only [d22773, d146837, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22774 q = 1) (hb : d146837 q = 1) : d149533 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22774, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22774, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22775 q = 1) (hb : d146837 q = 1) : d149534 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22775, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22775, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22776 q = 1) (hb : d146837 q = 1) : d149597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22776, d149597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22776, d149597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22694 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22695 q = 1) (hb : d146837 q = 1) : d149532 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d146837, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45957 q ha hb
    | true =>
      simp only [d22695, d146837, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22696 q = 1) (hb : d146837 q = 1) : d149533 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22697 q = 1) (hb : d146837 q = 1) : d149534 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22704 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22705 q = 1) (hb : d146837 q = 1) : d149536 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22705, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d22706 q = 1) (hb : d146837 q = 1) : d149537 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22707 q = 1) (hb : d146837 q = 1) : d149538 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d22708 q = 1) (hb : d146837 q = 1) : d149539 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22708, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22777 q = 1) (hb : d146837 q = 1) : d149598 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22777, d149598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22777, d149598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d22778 q = 1) (hb : d146837 q = 1) : d149599 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22778, d149599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22778, d149599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro50034 (p : Pattern) (ha : d22789 p = 1) (hb : d146837 p = 1) : d149605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22779 q = 1) (hb : d146837 q = 1) : d149600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22779, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50033 q ha hb
    | true =>
      simp only [d22779, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22780 q = 1) (hb : d146837 q = 1) : d149601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22780, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22780, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22784 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50021 q ha hb
    | true =>
      simp only [d22784, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22785 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22786 q = 1) (hb : d146837 q = 1) : d149602 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22786, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22786, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22787 q = 1) (hb : d146837 q = 1) : d149603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22787, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22787, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22788 q = 1) (hb : d146837 q = 1) : d149604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22788, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22788, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22789 q = 1) (hb : d146837 q = 1) : d149605 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22789, d149605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22789, d149605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50035 (p : Pattern) (ha : d22860 p = 1) (hb : d146837 p = 1) : d149542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22694 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22695 q = 1) (hb : d146837 q = 1) : d149532 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d146837, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45957 q ha hb
    | true =>
      simp only [d22695, d146837, d149532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22696 q = 1) (hb : d146837 q = 1) : d149533 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d149533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22697 q = 1) (hb : d146837 q = 1) : d149534 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d149534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22705 q = 1) (hb : d146837 q = 1) : d149536 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22705, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22706 q = 1) (hb : d146837 q = 1) : d149537 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22707 q = 1) (hb : d146837 q = 1) : d149538 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22708 q = 1) (hb : d146837 q = 1) : d149539 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22708, d149539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22854 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22855 q = 1) (hb : d146837 q = 1) : d149536 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22855, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45958 q ha hb
    | true =>
      simp only [d22855, d146837, d149536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22856 q = 1) (hb : d146837 q = 1) : d149537 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22856, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22856, d149537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22857 q = 1) (hb : d146837 q = 1) : d149538 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22857, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22857, d149538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22858 q = 1) (hb : d146837 q = 1) : d149540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22858, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22858, d149540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22859 q = 1) (hb : d146837 q = 1) : d149541 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22859, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22859, d149541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22860 q = 1) (hb : d146837 q = 1) : d149542 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22860, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22860, d149542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro50036 (p : Pattern) (ha : d22866 p = 1) (hb : d146837 p = 1) : d149611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22861 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22861, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50035 q ha hb
    | true =>
      simp only [d22861, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22862 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22862, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22862, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22863 q = 1) (hb : d146837 q = 1) : d149608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22863, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22863, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22864 q = 1) (hb : d146837 q = 1) : d149609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22864, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22864, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22865 q = 1) (hb : d146837 q = 1) : d149610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22865, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22865, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22866 q = 1) (hb : d146837 q = 1) : d149611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22866, d149611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22866, d149611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50037 (p : Pattern) (ha : d146837 p = 1) (hb : d150244 p = 1) : d149617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22754 q = 1) (hb : d146837 q = 1) : d149580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22754, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50029 q ha hb
    | true =>
      simp only [d22754, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50030 q ha hb
  have h2 (q : Pattern) (ha : d22755 q = 1) (hb : d146837 q = 1) : d149581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22755, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22755, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22756 q = 1) (hb : d146837 q = 1) : d149582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22756, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22756, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22757 q = 1) (hb : d146837 q = 1) : d149583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22757, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22757, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22764 q = 1) (hb : d146837 q = 1) : d149590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22764, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50031 q ha hb
    | true =>
      simp only [d22764, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50032 q ha hb
  have h6 (q : Pattern) (ha : d22765 q = 1) (hb : d146837 q = 1) : d149591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22765, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22765, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22766 q = 1) (hb : d146837 q = 1) : d149592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22766, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22766, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22794 q = 1) (hb : d146837 q = 1) : d149606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22794, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50034 q ha hb
    | true =>
      simp only [d22794, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50022 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150240 q = 1) : d149607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150240, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22867 q = 1) (hb : d146837 q = 1) : d149612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22867, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50036 q ha hb
    | true =>
      simp only [d22867, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22868 q = 1) (hb : d146837 q = 1) : d149613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22868, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22868, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150241 q = 1) : d149614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150241, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150242 q = 1) : d149615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150242, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150243 q = 1) : d149616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150243, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150244 q = 1) : d149617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150244, d149617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150244, d149617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro50038 (p : Pattern) (ha : d22873 p = 1) (hb : d146837 p = 1) : d149618 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50013 q ha hb
    | true =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146837 q = 1) : d149549 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d146837 q = 1) : d149550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22750 q = 1) (hb : d146837 q = 1) : d149576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22750, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22750, d149576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22873 q = 1) (hb : d146837 q = 1) : d149618 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22873, d149618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22873, d149618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50039 (p : Pattern) (ha : d22874 p = 1) (hb : d146837 p = 1) : d149619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146837 q = 1) : d149553 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d146837 q = 1) : d149554 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d149554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22752 q = 1) (hb : d146837 q = 1) : d149578 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22752, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22752, d149578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22874 q = 1) (hb : d146837 q = 1) : d149619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22874, d149619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22874, d149619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50040 (p : Pattern) (ha : d22879 p = 1) (hb : d146837 p = 1) : d149624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50013 q ha hb
    | true =>
      simp only [d22717, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d146837 q = 1) : d149549 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22758 q = 1) (hb : d146837 q = 1) : d149584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22758, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22758, d149584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22759 q = 1) (hb : d146837 q = 1) : d149585 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22759, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22759, d149585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22879 q = 1) (hb : d146837 q = 1) : d149624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22879, d149624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22879, d149624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50041 (p : Pattern) (ha : d22880 p = 1) (hb : d146837 p = 1) : d149625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d146837 q = 1) : d149553 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d149553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22761 q = 1) (hb : d146837 q = 1) : d149587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22761, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22761, d149587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22762 q = 1) (hb : d146837 q = 1) : d149588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22762, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22762, d149588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22880 q = 1) (hb : d146837 q = 1) : d149625 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22880, d149625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22880, d149625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50042 (p : Pattern) (ha : d22884 p = 1) (hb : d146837 p = 1) : d149629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22779 q = 1) (hb : d146837 q = 1) : d149600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22779, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50033 q ha hb
    | true =>
      simp only [d22779, d149600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22780 q = 1) (hb : d146837 q = 1) : d149601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22780, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22780, d149601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22784 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50021 q ha hb
    | true =>
      simp only [d22784, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22785 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22786 q = 1) (hb : d146837 q = 1) : d149602 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22786, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22786, d149602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22787 q = 1) (hb : d146837 q = 1) : d149603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22787, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22787, d149603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22788 q = 1) (hb : d146837 q = 1) : d149604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22788, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22788, d149604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22884 q = 1) (hb : d146837 q = 1) : d149629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22884, d149629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22884, d149629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50043 (p : Pattern) (ha : d22885 p = 1) (hb : d146837 p = 1) : d149565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22784 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50021 q ha hb
    | true =>
      simp only [d22784, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22785 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d146837 q = 1) : d149547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50014 q ha hb
    | true =>
      simp only [d22721, d149547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d146837 q = 1) : d149548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d149548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22790 q = 1) (hb : d146837 q = 1) : d149549 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22790, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22790, d149549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22791 q = 1) (hb : d146837 q = 1) : d149550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22791, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22791, d149550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22792 q = 1) (hb : d146837 q = 1) : d149551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22792, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22792, d149551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22885 q = 1) (hb : d146837 q = 1) : d149565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22885, d149565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22885, d149565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50044 (p : Pattern) (ha : d22891 p = 1) (hb : d146837 p = 1) : d149632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22861 q = 1) (hb : d146837 q = 1) : d149543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22861, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50035 q ha hb
    | true =>
      simp only [d22861, d149543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22862 q = 1) (hb : d146837 q = 1) : d149544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22862, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22862, d149544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22863 q = 1) (hb : d146837 q = 1) : d149608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22863, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22863, d149608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22864 q = 1) (hb : d146837 q = 1) : d149609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22864, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22864, d149609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22865 q = 1) (hb : d146837 q = 1) : d149610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22865, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22865, d149610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22891 q = 1) (hb : d146837 q = 1) : d149632 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22891, d149632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22891, d149632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50045 (p : Pattern) (ha : d146837 p = 1) (hb : d150249 p = 1) : d149638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22754 q = 1) (hb : d146837 q = 1) : d149580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22754, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50029 q ha hb
    | true =>
      simp only [d22754, d149580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50030 q ha hb
  have h2 (q : Pattern) (ha : d22755 q = 1) (hb : d146837 q = 1) : d149581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22755, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22755, d149581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22756 q = 1) (hb : d146837 q = 1) : d149582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22756, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22756, d149582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22757 q = 1) (hb : d146837 q = 1) : d149583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22757, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22757, d149583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22764 q = 1) (hb : d146837 q = 1) : d149590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22764, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50031 q ha hb
    | true =>
      simp only [d22764, d149590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50032 q ha hb
  have h6 (q : Pattern) (ha : d22765 q = 1) (hb : d146837 q = 1) : d149591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22765, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22765, d149591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22766 q = 1) (hb : d146837 q = 1) : d149592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22766, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22766, d149592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22794 q = 1) (hb : d146837 q = 1) : d149606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22794, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50034 q ha hb
    | true =>
      simp only [d22794, d149606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50022 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150240 q = 1) : d149607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150240, d149607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22867 q = 1) (hb : d146837 q = 1) : d149612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22867, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50036 q ha hb
    | true =>
      simp only [d22867, d149612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22868 q = 1) (hb : d146837 q = 1) : d149613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22868, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22868, d149613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150241 q = 1) : d149614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150241, d149614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150242 q = 1) : d149615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150242, d149615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150243 q = 1) : d149616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150243, d149616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22875 q = 1) (hb : d146837 q = 1) : d149620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22875, d149620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50038 q ha hb
    | true =>
      simp only [d22875, d149620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50039 q ha hb
  have h16 (q : Pattern) (ha : d22876 q = 1) (hb : d146837 q = 1) : d149621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22876, d149621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22876, d149621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22877 q = 1) (hb : d146837 q = 1) : d149622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22877, d149622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22877, d149622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22878 q = 1) (hb : d146837 q = 1) : d149623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22878, d149623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22878, d149623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22881 q = 1) (hb : d146837 q = 1) : d149626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22881, d149626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50040 q ha hb
    | true =>
      simp only [d22881, d149626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50041 q ha hb
  have h20 (q : Pattern) (ha : d22882 q = 1) (hb : d146837 q = 1) : d149627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22882, d149627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22882, d149627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d22883 q = 1) (hb : d146837 q = 1) : d149628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22883, d149628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d22883, d149628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d22886 q = 1) (hb : d146837 q = 1) : d149630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22886, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50042 q ha hb
    | true =>
      simp only [d22886, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50043 q ha hb
  have h23 (q : Pattern) (ha : d146837 q = 1) (hb : d150245 q = 1) : d149631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150245, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d22892 q = 1) (hb : d146837 q = 1) : d149633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22892, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50044 q ha hb
    | true =>
      simp only [d22892, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d22893 q = 1) (hb : d146837 q = 1) : d149634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22893, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d22893, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d146837 q = 1) (hb : d150246 q = 1) : d149635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150246, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d146837 q = 1) (hb : d150247 q = 1) : d149636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150247, d149636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150247, d149636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d146837 q = 1) (hb : d150248 q = 1) : d149637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150248, d149637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150248, d149637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146837 q = 1) (hb : d150249 q = 1) : d149638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150249, d149638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150249, d149638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro50046 (p : Pattern) (ha : d146837 p = 1) (hb : d150256 p = 1) : d149658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22886 q = 1) (hb : d146837 q = 1) : d149630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22886, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50042 q ha hb
    | true =>
      simp only [d22886, d149630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50043 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150245 q = 1) : d149631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150245, d149631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22892 q = 1) (hb : d146837 q = 1) : d149633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22892, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50044 q ha hb
    | true =>
      simp only [d22892, d149633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22893 q = 1) (hb : d146837 q = 1) : d149634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22893, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22893, d149634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150246 q = 1) : d149635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150246, d149635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150254 q = 1) : d149656 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150254, d149656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150254, d149656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150255 q = 1) : d149657 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150255, d149657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150255, d149657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150256 q = 1) : d149658 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150256, d149658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150256, d149658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50047 (p : Pattern) (ha : d22963 p = 1) (hb : d146837 p = 1) : d149681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22933 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22934 q = 1) (hb : d146837 q = 1) : d149667 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22934, d146837, d149667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45999 q ha hb
    | true =>
      simp only [d22934, d146837, d149667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22935 q = 1) (hb : d146837 q = 1) : d149668 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22935, d149668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22935, d149668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22936 q = 1) (hb : d146837 q = 1) : d149669 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22936, d149669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22936, d149669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22938 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22939 q = 1) (hb : d146837 q = 1) : d149671 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22939, d146837, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46000 q ha hb
    | true =>
      simp only [d22939, d146837, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22940 q = 1) (hb : d146837 q = 1) : d149672 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22940, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22940, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22941 q = 1) (hb : d146837 q = 1) : d149673 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22941, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22941, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22942 q = 1) (hb : d146837 q = 1) : d149674 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22942, d149674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22942, d149674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22948 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22949 q = 1) (hb : d146837 q = 1) : d149671 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d146837, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46000 q ha hb
    | true =>
      simp only [d22949, d146837, d149671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22950 q = 1) (hb : d146837 q = 1) : d149672 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d149672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22951 q = 1) (hb : d146837 q = 1) : d149673 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d149673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22957 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22958 q = 1) (hb : d146837 q = 1) : d149676 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d146837, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45974 q ha hb
    | true =>
      simp only [d22958, d146837, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d22959 q = 1) (hb : d146837 q = 1) : d149677 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22960 q = 1) (hb : d146837 q = 1) : d149678 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d22961 q = 1) (hb : d146837 q = 1) : d149679 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22961, d149679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22962 q = 1) (hb : d146837 q = 1) : d149680 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22962, d149680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22962, d149680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d22963 q = 1) (hb : d146837 q = 1) : d149681 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22963, d149681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22963, d149681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro50048 (p : Pattern) (ha : d22968 p = 1) (hb : d146837 p = 1) : d149686 p = 1 := by
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
  have h10 (q : Pattern) (ha : d22966 q = 1) (hb : d146837 q = 1) : d149684 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22966, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22966, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22967 q = 1) (hb : d146837 q = 1) : d149685 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22967, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22967, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22968 q = 1) (hb : d146837 q = 1) : d149686 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22968, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22968, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro50049 (p : Pattern) (ha : d22974 p = 1) (hb : d146837 p = 1) : d149692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22964 q = 1) (hb : d146837 q = 1) : d149682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22964, d149682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50047 q ha hb
    | true =>
      simp only [d22964, d149682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22965 q = 1) (hb : d146837 q = 1) : d149683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22965, d149683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22965, d149683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22969 q = 1) (hb : d146837 q = 1) : d149687 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22969, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50048 q ha hb
    | true =>
      simp only [d22969, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22970 q = 1) (hb : d146837 q = 1) : d149688 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22970, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22970, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22971 q = 1) (hb : d146837 q = 1) : d149689 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22971, d149689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22971, d149689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22972 q = 1) (hb : d146837 q = 1) : d149690 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22972, d149690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22972, d149690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22973 q = 1) (hb : d146837 q = 1) : d149691 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22973, d149691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22973, d149691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22974 q = 1) (hb : d146837 q = 1) : d149692 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22974, d149692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22974, d149692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50050 (p : Pattern) (ha : d22988 p = 1) (hb : d146837 p = 1) : d149700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22969 q = 1) (hb : d146837 q = 1) : d149687 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22969, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50048 q ha hb
    | true =>
      simp only [d22969, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22970 q = 1) (hb : d146837 q = 1) : d149688 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22970, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22970, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d22985 q = 1) (hb : d146837 q = 1) : d149697 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22985, d149697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22985, d149697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22986 q = 1) (hb : d146837 q = 1) : d149698 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22986, d149698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22986, d149698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22987 q = 1) (hb : d146837 q = 1) : d149699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22987, d149699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22987, d149699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22988 q = 1) (hb : d146837 q = 1) : d149700 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22988, d149700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22988, d149700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro50051 (p : Pattern) (ha : d23051 p = 1) (hb : d146837 p = 1) : d149686 p = 1 := by
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
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23045 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d23046 q = 1) (hb : d146837 q = 1) : d149676 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23046, d146837, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45974 q ha hb
    | true =>
      simp only [d23046, d146837, d149676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d23047 q = 1) (hb : d146837 q = 1) : d149677 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23047, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23047, d149677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23048 q = 1) (hb : d146837 q = 1) : d149678 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23048, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23048, d149678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23049 q = 1) (hb : d146837 q = 1) : d149684 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23049, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23049, d149684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d23050 q = 1) (hb : d146837 q = 1) : d149685 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23050, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23050, d149685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23051 q = 1) (hb : d146837 q = 1) : d149686 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23051, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23051, d149686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro50052 (p : Pattern) (ha : d23057 p = 1) (hb : d146837 p = 1) : d149706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23052 q = 1) (hb : d146837 q = 1) : d149687 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23052, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50051 q ha hb
    | true =>
      simp only [d23052, d149687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23053 q = 1) (hb : d146837 q = 1) : d149688 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23053, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23053, d149688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23054 q = 1) (hb : d146837 q = 1) : d149703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23054, d149703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23054, d149703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23055 q = 1) (hb : d146837 q = 1) : d149704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23055, d149704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23055, d149704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23056 q = 1) (hb : d146837 q = 1) : d149705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23056, d149705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23056, d149705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23057 q = 1) (hb : d146837 q = 1) : d149706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23057, d149706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23057, d149706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro50053 (p : Pattern) (ha : d146837 p = 1) (hb : d150266 p = 1) : d149712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22989 q = 1) (hb : d146837 q = 1) : d149701 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22989, d149701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50049 q ha hb
    | true =>
      simp only [d22989, d149701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50050 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150262 q = 1) : d149702 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150262, d149702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150262, d149702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23058 q = 1) (hb : d146837 q = 1) : d149707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23058, d149707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50052 q ha hb
    | true =>
      simp only [d23058, d149707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23059 q = 1) (hb : d146837 q = 1) : d149708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23059, d149708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23059, d149708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150263 q = 1) : d149709 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150263, d149709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150263, d149709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150264 q = 1) : d149710 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150264, d149710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150264, d149710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150265 q = 1) : d149711 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150265, d149711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150265, d149711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150266 q = 1) : d149712 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150266, d149712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150266, d149712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50054 (p : Pattern) (ha : d146837 p = 1) (hb : d150272 p = 1) : d149729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22737 q = 1) (hb : d146837 q = 1) : d149563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22737, d149563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22737, d149563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50017 q ha hb
  have h2 (q : Pattern) (ha : d22738 q = 1) (hb : d146837 q = 1) : d149564 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22738, d149564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22738, d149564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22747 q = 1) (hb : d146837 q = 1) : d149573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50017 q ha hb
    | true =>
      simp only [d22747, d149573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50020 q ha hb
  have h4 (q : Pattern) (ha : d22748 q = 1) (hb : d146837 q = 1) : d149574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22748, d149574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22749 q = 1) (hb : d146837 q = 1) : d149575 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d22749, d149575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22749, d149575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150250 q = 1) : d149639 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150250, d149639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50037 q ha hb
    | true =>
      simp only [d150250, d149639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50045 q ha hb
  have h7 (q : Pattern) (ha : d22916 q = 1) (hb : d146837 q = 1) : d149652 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22916, d149652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50023 q ha hb
    | true =>
      simp only [d22916, d149652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50024 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150251 q = 1) : d149653 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150251, d149653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150251, d149653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150252 q = 1) : d149654 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150252, d149654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150252, d149654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d150253 q = 1) : d149655 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150253, d149655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150253, d149655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d150257 q = 1) : d149659 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150257, d149659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150257, d149659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50046 q ha hb
  have h12 (q : Pattern) (ha : d22925 q = 1) (hb : d146837 q = 1) : d149661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22925, d149661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22925, d149661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50025 q ha hb
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150258 q = 1) : d149662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150258, d149662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150258, d149662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150259 q = 1) : d149663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150259, d149663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150259, d149663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150260 q = 1) : d149664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150260, d149664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150260, d149664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d150261 q = 1) : d149665 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150261, d149665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150261, d149665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146837 q = 1) (hb : d150267 q = 1) : d149713 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150267, d149713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150267, d149713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50053 q ha hb
  have h18 (q : Pattern) (ha : d23075 q = 1) (hb : d146837 q = 1) : d149724 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23075, d149724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23075, d149724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50028 q ha hb
  have h19 (q : Pattern) (ha : d146837 q = 1) (hb : d150268 q = 1) : d149725 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150268, d149725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150268, d149725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d146837 q = 1) (hb : d150269 q = 1) : d149726 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150269, d149726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150269, d149726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d146837 q = 1) (hb : d150270 q = 1) : d149727 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150270, d149727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150270, d149727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d146837 q = 1) (hb : d150271 q = 1) : d149728 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150271, d149728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150271, d149728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146837 q = 1) (hb : d150272 q = 1) : d149729 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150272, d149729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150272, d149729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro50055 (p : Pattern) (ha : d146837 p = 1) (hb : d150278 p = 1) : d149735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150273 q = 1) : d149730 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150273, d149730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150273, d149730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50054 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150274 q = 1) : d149731 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150274, d149731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150274, d149731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150275 q = 1) : d149732 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150275, d149732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150275, d149732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150276 q = 1) : d149733 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150276, d149733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150276, d149733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150277 q = 1) : d149734 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150277, d149734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150277, d149734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150278 q = 1) : d149735 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150278, d149735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150278, d149735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50056 (p : Pattern) (ha : d146837 p = 1) (hb : d150284 p = 1) : d149741 p = 1 := by
  have h0 (q : Pattern) (ha : d146837 q = 1) (hb : d150113 q = 1) : d148924 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150113, d148924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49850 q ha hb
    | true =>
      simp only [d150113, d148924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49888 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150153 q = 1) : d149112 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150153, d149112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150153, d149112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49926 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150154 q = 1) : d149113 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150154, d149113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150154, d149113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150194 q = 1) : d149319 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150194, d149319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150194, d149319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49969 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150195 q = 1) : d149320 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150195, d149320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150195, d149320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150196 q = 1) : d149321 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150196, d149321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150196, d149321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150236 q = 1) : d149527 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150236, d149527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150236, d149527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50012 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150237 q = 1) : d149528 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150237, d149528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150237, d149528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150238 q = 1) : d149529 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150238, d149529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150238, d149529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d150239 q = 1) : d149530 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150239, d149530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150239, d149530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d150279 q = 1) : d149736 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150279, d149736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150279, d149736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50055 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150280 q = 1) : d149737 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150280, d149737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150280, d149737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150281 q = 1) : d149738 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150281, d149738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150281, d149738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150282 q = 1) : d149739 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150282, d149739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150282, d149739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150283 q = 1) : d149740 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150283, d149740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150283, d149740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d150284 q = 1) : d149741 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150284, d149741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150284, d149741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro50057 (p : Pattern) (ha : d146837 p = 1) (hb : d150290 p = 1) : d149747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150285 q = 1) : d149742 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150285, d149742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50056 q ha hb
    | true =>
      simp only [d150285, d149742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150286 q = 1) : d149743 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150286, d149743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150286, d149743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150287 q = 1) : d149744 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150287, d149744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150287, d149744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150288 q = 1) : d149745 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150288, d149745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150288, d149745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150289 q = 1) : d149746 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150289, d149746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150289, d149746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150290 q = 1) : d149747 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150290, d149747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150290, d149747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50058 (p : Pattern) (ha : d146837 p = 1) (hb : d150296 p = 1) : d149753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150291 q = 1) : d149748 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150291, d149748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50057 q ha hb
    | true =>
      simp only [d150291, d149748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150292 q = 1) : d149749 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150292, d149749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150292, d149749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150293 q = 1) : d149750 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150293, d149750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150293, d149750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150294 q = 1) : d149751 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150294, d149751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150294, d149751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150295 q = 1) : d149752 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150295, d149752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150295, d149752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150296 q = 1) : d149753 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150296, d149753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150296, d149753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50059 (p : Pattern) (ha : d146837 p = 1) (hb : d150302 p = 1) : d149759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150297 q = 1) : d149754 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150297, d149754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50058 q ha hb
    | true =>
      simp only [d150297, d149754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150298 q = 1) : d149755 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150298, d149755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150298, d149755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150299 q = 1) : d149756 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150299, d149756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150299, d149756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150300 q = 1) : d149757 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150300, d149757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150300, d149757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150301 q = 1) : d149758 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150301, d149758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150301, d149758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150302 q = 1) : d149759 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150302, d149759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150302, d149759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50060 (p : Pattern) (ha : d146837 p = 1) (hb : d150308 p = 1) : d149765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150303 q = 1) : d149760 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150303, d149760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50059 q ha hb
    | true =>
      simp only [d150303, d149760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150304 q = 1) : d149761 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150304, d149761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150304, d149761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150305 q = 1) : d149762 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150305, d149762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150305, d149762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150306 q = 1) : d149763 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150306, d149763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150306, d149763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150307 q = 1) : d149764 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150307, d149764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150307, d149764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150308 q = 1) : d149765 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150308, d149765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150308, d149765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50061 (p : Pattern) (ha : d146837 p = 1) (hb : d150314 p = 1) : d149771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150309 q = 1) : d149766 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150309, d149766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50060 q ha hb
    | true =>
      simp only [d150309, d149766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150310 q = 1) : d149767 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150310, d149767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150310, d149767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150311 q = 1) : d149768 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150311, d149768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150311, d149768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150312 q = 1) : d149769 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150312, d149769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150312, d149769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150313 q = 1) : d149770 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150313, d149770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150313, d149770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150314 q = 1) : d149771 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150314, d149771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150314, d149771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50062 (p : Pattern) (ha : d146837 p = 1) (hb : d150320 p = 1) : d149777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150315 q = 1) : d149772 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150315, d149772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50061 q ha hb
    | true =>
      simp only [d150315, d149772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150316 q = 1) : d149773 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150316, d149773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150316, d149773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150317 q = 1) : d149774 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150317, d149774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150317, d149774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150318 q = 1) : d149775 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150318, d149775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150318, d149775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150319 q = 1) : d149776 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150319, d149776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150319, d149776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150320 q = 1) : d149777 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150320, d149777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150320, d149777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50063 (p : Pattern) (ha : d146837 p = 1) (hb : d150326 p = 1) : d149783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150321 q = 1) : d149778 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150321, d149778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50062 q ha hb
    | true =>
      simp only [d150321, d149778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150322 q = 1) : d149779 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150322, d149779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150322, d149779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150323 q = 1) : d149780 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150323, d149780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150323, d149780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150324 q = 1) : d149781 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150324, d149781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150324, d149781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150325 q = 1) : d149782 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150325, d149782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150325, d149782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150326 q = 1) : d149783 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150326, d149783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150326, d149783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50064 (p : Pattern) (ha : d51995 p = 1) (hb : d148547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20892 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20892, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20892, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51995 q = 1) (hb : d148547 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d51995, d148547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d51995, d148547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50065 (p : Pattern) (ha : d107491 p = 1) (hb : d148553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107486 q = 1) (hb : d148548 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107486, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50064 q ha hb
    | true =>
      simp only [d107486, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107487 q = 1) (hb : d148549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107487, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107487, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107488 q = 1) (hb : d148550 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107488, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107488, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d107489 q = 1) (hb : d148551 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107489, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107489, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
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
  have h9 (q : Pattern) (ha : d107490 q = 1) (hb : d148552 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107490, d148552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107490, d148552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107491 q = 1) (hb : d148553 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107491, d148553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107491, d148553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50066 (p : Pattern) (ha : d107497 p = 1) (hb : d148559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d148554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50065 q ha hb
    | true =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d148555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d148556 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107495 q = 1) (hb : d148557 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107495, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107495, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107496 q = 1) (hb : d148558 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107496, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107496, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107497 q = 1) (hb : d148559 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107497, d148559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107497, d148559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50067 (p : Pattern) (ha : d107503 p = 1) (hb : d148565 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d107498 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50066 q ha hb
    | true =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107499 q = 1) (hb : d148561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107499, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107499, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d107500 q = 1) (hb : d148562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107500, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107500, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107501 q = 1) (hb : d148563 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107501, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107501, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107502 q = 1) (hb : d148564 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107502, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107502, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107503 q = 1) (hb : d148565 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107503, d148565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107503, d148565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro50068 (p : Pattern) (ha : d107504 p = 1) (hb : d148566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d148554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50065 q ha hb
    | true =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d148555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d148556 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107495 q = 1) (hb : d148557 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107495, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107495, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107496 q = 1) (hb : d148558 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107496, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107496, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107504 q = 1) (hb : d148566 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107504, d148566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107504, d148566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50069 (p : Pattern) (ha : d107510 p = 1) (hb : d148572 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d107498 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50066 q ha hb
    | true =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107499 q = 1) (hb : d148561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107499, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107499, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d107500 q = 1) (hb : d148562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107500, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107500, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107501 q = 1) (hb : d148563 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107501, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107501, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107502 q = 1) (hb : d148564 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107502, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107502, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d107505 q = 1) (hb : d148567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50068 q ha hb
    | true =>
      simp only [d107505, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107506 q = 1) (hb : d148568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107506, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d107506, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d107507 q = 1) (hb : d148569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107507, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107507, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d107508 q = 1) (hb : d148570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107508, d148570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d107508, d148570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107509 q = 1) (hb : d148571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107509, d148571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d107509, d148571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107510 q = 1) (hb : d148572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107510, d148572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107510, d148572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro50070 (p : Pattern) (ha : d107517 p = 1) (hb : d148579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107505 q = 1) (hb : d148567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50068 q ha hb
    | true =>
      simp only [d107505, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107506 q = 1) (hb : d148568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107506, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107506, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d107507 q = 1) (hb : d148569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107507, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107507, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107515 q = 1) (hb : d148577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107515, d148577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107515, d148577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107516 q = 1) (hb : d148578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107516, d148578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107516, d148578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107517 q = 1) (hb : d148579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107517, d148579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107517, d148579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50071 (p : Pattern) (ha : d52049 p = 1) (hb : d148585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20931 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20931, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20931, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52049 q = 1) (hb : d148585 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52049, d148585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52049, d148585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50072 (p : Pattern) (ha : d107528 p = 1) (hb : d148591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107523 q = 1) (hb : d148586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107523, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50071 q ha hb
    | true =>
      simp only [d107523, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107524 q = 1) (hb : d148587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107524, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107524, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107525 q = 1) (hb : d148588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107525, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107525, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d107526 q = 1) (hb : d148589 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107526, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107526, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
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
  have h9 (q : Pattern) (ha : d107527 q = 1) (hb : d148590 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107527, d148590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107527, d148590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107528 q = 1) (hb : d148591 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107528, d148591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107528, d148591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50073 (p : Pattern) (ha : d107534 p = 1) (hb : d148597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107529 q = 1) (hb : d148592 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107529, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50072 q ha hb
    | true =>
      simp only [d107529, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107530 q = 1) (hb : d148593 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107530, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107530, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d107531 q = 1) (hb : d148594 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107531, d148594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107531, d148594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107532 q = 1) (hb : d148595 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107532, d148595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107532, d148595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107533 q = 1) (hb : d148596 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107533, d148596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107533, d148596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107534 q = 1) (hb : d148597 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107534, d148597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107534, d148597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50074 (p : Pattern) (ha : d107540 p = 1) (hb : d148603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107535 q = 1) (hb : d148598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107535, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50073 q ha hb
    | true =>
      simp only [d107535, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107536 q = 1) (hb : d148599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107536, d148599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107536, d148599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d107537 q = 1) (hb : d148600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107537, d148600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107537, d148600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107538 q = 1) (hb : d148601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107538, d148601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107538, d148601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107539 q = 1) (hb : d148602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107539, d148602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107539, d148602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107540 q = 1) (hb : d148603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107540, d148603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107540, d148603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50075 (p : Pattern) (ha : d107546 p = 1) (hb : d148609 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d107511 q = 1) (hb : d148573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107511, d148573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50067 q ha hb
    | true =>
      simp only [d107511, d148573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50069 q ha hb
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
  have h8 (q : Pattern) (ha : d107512 q = 1) (hb : d148574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107512, d148574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107512, d148574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d107513 q = 1) (hb : d148575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107513, d148575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107513, d148575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107514 q = 1) (hb : d148576 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107514, d148576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d107514, d148576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107518 q = 1) (hb : d148580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107518, d148580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107518, d148580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50070 q ha hb
  have h12 (q : Pattern) (ha : d107519 q = 1) (hb : d148581 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107519, d148581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107519, d148581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107520 q = 1) (hb : d148582 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107520, d148582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107520, d148582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d107521 q = 1) (hb : d148583 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107521, d148583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107521, d148583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107522 q = 1) (hb : d148584 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107522, d148584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107522, d148584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107541 q = 1) (hb : d148604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107541, d148604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107541, d148604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50074 q ha hb
  have h17 (q : Pattern) (ha : d107542 q = 1) (hb : d148605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107542, d148605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107542, d148605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d107543 q = 1) (hb : d148606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107543, d148606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107543, d148606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107544 q = 1) (hb : d148607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107544, d148607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d107544, d148607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d107545 q = 1) (hb : d148608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107545, d148608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107545, d148608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107546 q = 1) (hb : d148609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107546, d148609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107546, d148609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro50076 (p : Pattern) (ha : d107556 p = 1) (hb : d148619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107498 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50066 q ha hb
    | true =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d107552 q = 1) (hb : d148615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107552, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107552, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107553 q = 1) (hb : d148616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107553, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107553, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107554 q = 1) (hb : d148617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107554, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107554, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107555 q = 1) (hb : d148618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107555, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107555, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107556 q = 1) (hb : d148619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107556, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107556, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50077 (p : Pattern) (ha : d107563 p = 1) (hb : d148626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107498 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50066 q ha hb
    | true =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d107552 q = 1) (hb : d148615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107552, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107552, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107553 q = 1) (hb : d148616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107553, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107553, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107554 q = 1) (hb : d148617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107554, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107554, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107555 q = 1) (hb : d148618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107555, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107555, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107505 q = 1) (hb : d148567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50068 q ha hb
    | true =>
      simp only [d107505, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d107559 q = 1) (hb : d148622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107559, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107559, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107560 q = 1) (hb : d148623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107560, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107560, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107561 q = 1) (hb : d148624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107561, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107561, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107562 q = 1) (hb : d148625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107562, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107562, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107563 q = 1) (hb : d148626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107563, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107563, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50078 (p : Pattern) (ha : d107568 p = 1) (hb : d148631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d148554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50065 q ha hb
    | true =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d148555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d148556 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107495 q = 1) (hb : d148557 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107495, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107495, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107567 q = 1) (hb : d148630 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107567, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107567, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107568 q = 1) (hb : d148631 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107568, d148631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107568, d148631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50079 (p : Pattern) (ha : d107575 p = 1) (hb : d148638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d148554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50065 q ha hb
    | true =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d148555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d148556 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107573 q = 1) (hb : d148636 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107573, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107573, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107574 q = 1) (hb : d148637 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107574, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107574, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107575 q = 1) (hb : d148638 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107575, d148638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107575, d148638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50080 (p : Pattern) (ha : d52123 p = 1) (hb : d148642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20994 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20994, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52123 q = 1) (hb : d148642 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52123, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52123, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50081 (p : Pattern) (ha : d107584 p = 1) (hb : d148648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107579 q = 1) (hb : d148643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107579, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50080 q ha hb
    | true =>
      simp only [d107579, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107580 q = 1) (hb : d148644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107580, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107580, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107581 q = 1) (hb : d148645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107581, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107581, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107486 q = 1) (hb : d148548 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107486, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50064 q ha hb
    | true =>
      simp only [d107486, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107487 q = 1) (hb : d148549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107487, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107487, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107488 q = 1) (hb : d148550 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107488, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107488, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107582 q = 1) (hb : d148646 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107582, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107582, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d107489 q = 1) (hb : d148551 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107489, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107489, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d107583 q = 1) (hb : d148647 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107583, d148647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107583, d148647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107584 q = 1) (hb : d148648 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107584, d148648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107584, d148648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50082 (p : Pattern) (ha : d107590 p = 1) (hb : d148654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107585 q = 1) (hb : d148649 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107585, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50081 q ha hb
    | true =>
      simp only [d107585, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107586 q = 1) (hb : d148650 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107586, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107586, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107492 q = 1) (hb : d148554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50065 q ha hb
    | true =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107493 q = 1) (hb : d148555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107587 q = 1) (hb : d148651 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107587, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107587, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107588 q = 1) (hb : d148652 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107588, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107588, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107589 q = 1) (hb : d148653 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107589, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107589, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107590 q = 1) (hb : d148654 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107590, d148654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107590, d148654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50083 (p : Pattern) (ha : d107596 p = 1) (hb : d148660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d148554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50065 q ha hb
    | true =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d148555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107593 q = 1) (hb : d148657 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107593, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107593, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107594 q = 1) (hb : d148658 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107594, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107594, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107595 q = 1) (hb : d148659 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107595, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107595, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107596 q = 1) (hb : d148660 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107596, d148660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107596, d148660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50084 (p : Pattern) (ha : d107602 p = 1) (hb : d148666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107569 q = 1) (hb : d148632 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107569, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50078 q ha hb
    | true =>
      simp only [d107569, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d107570 q = 1) (hb : d148633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107570, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107570, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107571 q = 1) (hb : d148634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107571, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107571, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107572 q = 1) (hb : d148635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107572, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107572, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107576 q = 1) (hb : d148639 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107576, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50079 q ha hb
    | true =>
      simp only [d107576, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d107577 q = 1) (hb : d148640 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107577, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107577, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107578 q = 1) (hb : d148641 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107578, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107578, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107591 q = 1) (hb : d148655 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107591, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50082 q ha hb
    | true =>
      simp only [d107591, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50066 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107592 q = 1) (hb : d148656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107592, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107597 q = 1) (hb : d148661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107597, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50083 q ha hb
    | true =>
      simp only [d107597, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107598 q = 1) (hb : d148662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107598, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107598, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107599 q = 1) (hb : d148663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107599, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107600 q = 1) (hb : d148664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107600, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107601 q = 1) (hb : d148665 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107601, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107602 q = 1) (hb : d148666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107602, d148666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107602, d148666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro50085 (p : Pattern) (ha : d107603 p = 1) (hb : d148667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d148554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50065 q ha hb
    | true =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d148555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d148556 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107495 q = 1) (hb : d148557 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107495, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107495, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107567 q = 1) (hb : d148630 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107567, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107567, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107603 q = 1) (hb : d148667 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107603, d148667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107603, d148667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50086 (p : Pattern) (ha : d107608 p = 1) (hb : d148672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d148554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50065 q ha hb
    | true =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d148555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d148556 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107573 q = 1) (hb : d148636 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107573, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107573, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107574 q = 1) (hb : d148637 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107574, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107574, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107608 q = 1) (hb : d148672 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107608, d148672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107608, d148672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50087 (p : Pattern) (ha : d107612 p = 1) (hb : d148676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107585 q = 1) (hb : d148649 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107585, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50081 q ha hb
    | true =>
      simp only [d107585, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107586 q = 1) (hb : d148650 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107586, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107586, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107492 q = 1) (hb : d148554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50065 q ha hb
    | true =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107493 q = 1) (hb : d148555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107587 q = 1) (hb : d148651 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107587, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107587, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107588 q = 1) (hb : d148652 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107588, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107588, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107589 q = 1) (hb : d148653 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107589, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107589, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107612 q = 1) (hb : d148676 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107612, d148676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107612, d148676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50088 (p : Pattern) (ha : d107615 p = 1) (hb : d148679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d148554 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50065 q ha hb
    | true =>
      simp only [d107492, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d148555 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107593 q = 1) (hb : d148657 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107593, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107593, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107594 q = 1) (hb : d148658 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107594, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107594, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107595 q = 1) (hb : d148659 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107595, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107595, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107615 q = 1) (hb : d148679 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107615, d148679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107615, d148679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50089 (p : Pattern) (ha : d107621 p = 1) (hb : d148685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107569 q = 1) (hb : d148632 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107569, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50078 q ha hb
    | true =>
      simp only [d107569, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d107570 q = 1) (hb : d148633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107570, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107570, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107571 q = 1) (hb : d148634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107571, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107571, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107572 q = 1) (hb : d148635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107572, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107572, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107576 q = 1) (hb : d148639 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107576, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50079 q ha hb
    | true =>
      simp only [d107576, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d107577 q = 1) (hb : d148640 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107577, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107577, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107578 q = 1) (hb : d148641 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107578, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107578, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107591 q = 1) (hb : d148655 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107591, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50082 q ha hb
    | true =>
      simp only [d107591, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50066 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107592 q = 1) (hb : d148656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107592, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107597 q = 1) (hb : d148661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107597, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50083 q ha hb
    | true =>
      simp only [d107597, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107598 q = 1) (hb : d148662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107598, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107598, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107599 q = 1) (hb : d148663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107599, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107600 q = 1) (hb : d148664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107600, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107601 q = 1) (hb : d148665 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107601, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107604 q = 1) (hb : d148668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107604, d148668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50085 q ha hb
    | true =>
      simp only [d107604, d148668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d107605 q = 1) (hb : d148669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107605, d148669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107605, d148669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107606 q = 1) (hb : d148670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107606, d148670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107606, d148670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107607 q = 1) (hb : d148671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107607, d148671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107607, d148671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d107609 q = 1) (hb : d148673 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107609, d148673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50086 q ha hb
    | true =>
      simp only [d107609, d148673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d107610 q = 1) (hb : d148674 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107610, d148674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107610, d148674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d107611 q = 1) (hb : d148675 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107611, d148675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107611, d148675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107613 q = 1) (hb : d148677 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107613, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50087 q ha hb
    | true =>
      simp only [d107613, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50068 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d107505 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107614 q = 1) (hb : d148678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d107614, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d107616 q = 1) (hb : d148680 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107616, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50088 q ha hb
    | true =>
      simp only [d107616, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d107617 q = 1) (hb : d148681 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107617, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d107617, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d107618 q = 1) (hb : d148682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107618, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d107619 q = 1) (hb : d148683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107619, d148683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d107619, d148683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107620 q = 1) (hb : d148684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107620, d148684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107620, d148684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107621 q = 1) (hb : d148685 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107621, d148685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107621, d148685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro50090 (p : Pattern) (ha : d107623 p = 1) (hb : d148687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107498 q = 1) (hb : d148560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50066 q ha hb
    | true =>
      simp only [d107498, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d107552 q = 1) (hb : d148615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107552, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107552, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107553 q = 1) (hb : d148616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107553, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107553, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107554 q = 1) (hb : d148617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107554, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107554, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107555 q = 1) (hb : d148618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107555, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107555, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d107623 q = 1) (hb : d148687 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107623, d148687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107623, d148687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50091 (p : Pattern) (ha : d107630 p = 1) (hb : d148694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107613 q = 1) (hb : d148677 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107613, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50087 q ha hb
    | true =>
      simp only [d107613, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50068 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107505 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107614 q = 1) (hb : d148678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107614, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107616 q = 1) (hb : d148680 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107616, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50088 q ha hb
    | true =>
      simp only [d107616, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107617 q = 1) (hb : d148681 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107617, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107617, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107618 q = 1) (hb : d148682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107618, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107628 q = 1) (hb : d148692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107628, d148692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107628, d148692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107629 q = 1) (hb : d148693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107629, d148693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107629, d148693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107630 q = 1) (hb : d148694 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107630, d148694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107630, d148694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50092 (p : Pattern) (ha : d52183 p = 1) (hb : d148700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33341 q ha hb
    | true =>
      simp only [d751, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21075 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21075, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52183 q = 1) (hb : d148700 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52183, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52183, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50093 (p : Pattern) (ha : d107641 p = 1) (hb : d148706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107636 q = 1) (hb : d148701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107636, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50092 q ha hb
    | true =>
      simp only [d107636, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107637 q = 1) (hb : d148702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107637, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107637, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107638 q = 1) (hb : d148703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107638, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107638, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107523 q = 1) (hb : d148586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107523, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50071 q ha hb
    | true =>
      simp only [d107523, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107524 q = 1) (hb : d148587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107524, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107524, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107525 q = 1) (hb : d148588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107525, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107525, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107639 q = 1) (hb : d148704 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107639, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107639, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107526 q = 1) (hb : d148589 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107526, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107526, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d107640 q = 1) (hb : d148705 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107640, d148705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107640, d148705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107641 q = 1) (hb : d148706 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107641, d148706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107641, d148706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50094 (p : Pattern) (ha : d107647 p = 1) (hb : d148712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107642 q = 1) (hb : d148707 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107642, d148707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50093 q ha hb
    | true =>
      simp only [d107642, d148707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107643 q = 1) (hb : d148708 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107643, d148708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107643, d148708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107529 q = 1) (hb : d148592 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107529, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50072 q ha hb
    | true =>
      simp only [d107529, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107530 q = 1) (hb : d148593 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107530, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107530, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107644 q = 1) (hb : d148709 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107644, d148709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107644, d148709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107645 q = 1) (hb : d148710 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107645, d148710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107645, d148710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107646 q = 1) (hb : d148711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107646, d148711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107646, d148711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107647 q = 1) (hb : d148712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107647, d148712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107647, d148712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50095 (p : Pattern) (ha : d107653 p = 1) (hb : d148718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107529 q = 1) (hb : d148592 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107529, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50072 q ha hb
    | true =>
      simp only [d107529, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107530 q = 1) (hb : d148593 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107530, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107530, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107650 q = 1) (hb : d148715 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107650, d148715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107650, d148715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107651 q = 1) (hb : d148716 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107651, d148716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107651, d148716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107652 q = 1) (hb : d148717 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107652, d148717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107652, d148717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107653 q = 1) (hb : d148718 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107653, d148718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107653, d148718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50096 (p : Pattern) (ha : d107659 p = 1) (hb : d148724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107648 q = 1) (hb : d148713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107648, d148713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50094 q ha hb
    | true =>
      simp only [d107648, d148713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50073 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107535 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107649 q = 1) (hb : d148714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107649, d148714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107649, d148714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107654 q = 1) (hb : d148719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107654, d148719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50095 q ha hb
    | true =>
      simp only [d107654, d148719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107655 q = 1) (hb : d148720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107655, d148720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107655, d148720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107656 q = 1) (hb : d148721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107656, d148721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107656, d148721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107657 q = 1) (hb : d148722 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107657, d148722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107657, d148722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107658 q = 1) (hb : d148723 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107658, d148723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107658, d148723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107659 q = 1) (hb : d148724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107659, d148724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107659, d148724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50097 (p : Pattern) (ha : d107665 p = 1) (hb : d148730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107557 q = 1) (hb : d148620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107557, d148620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107557, d148620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50076 q ha hb
  have h2 (q : Pattern) (ha : d107558 q = 1) (hb : d148621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107558, d148621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107558, d148621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107564 q = 1) (hb : d148627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107564, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50076 q ha hb
    | true =>
      simp only [d107564, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50077 q ha hb
  have h4 (q : Pattern) (ha : d107565 q = 1) (hb : d148628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107565, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107565, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107566 q = 1) (hb : d148629 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107566, d148629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107566, d148629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107622 q = 1) (hb : d148686 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107622, d148686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50084 q ha hb
    | true =>
      simp only [d107622, d148686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50089 q ha hb
  have h7 (q : Pattern) (ha : d107624 q = 1) (hb : d148688 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107624, d148688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50090 q ha hb
    | true =>
      simp only [d107624, d148688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d107625 q = 1) (hb : d148689 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107625, d148689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107625, d148689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107626 q = 1) (hb : d148690 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107626, d148690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107626, d148690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107627 q = 1) (hb : d148691 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107627, d148691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107627, d148691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107631 q = 1) (hb : d148695 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107631, d148695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107631, d148695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50091 q ha hb
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
  have h13 (q : Pattern) (ha : d107632 q = 1) (hb : d148696 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107632, d148696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107632, d148696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107633 q = 1) (hb : d148697 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107633, d148697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107633, d148697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107634 q = 1) (hb : d148698 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107634, d148698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107634, d148698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107635 q = 1) (hb : d148699 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107635, d148699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107635, d148699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107660 q = 1) (hb : d148725 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107660, d148725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107660, d148725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50096 q ha hb
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
  have h19 (q : Pattern) (ha : d107661 q = 1) (hb : d148726 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107661, d148726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107661, d148726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d107662 q = 1) (hb : d148727 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107662, d148727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107662, d148727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107663 q = 1) (hb : d148728 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107663, d148728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d107663, d148728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107664 q = 1) (hb : d148729 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107664, d148729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107664, d148729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107665 q = 1) (hb : d148730 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107665, d148730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107665, d148730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro50098 (p : Pattern) (ha : d107671 p = 1) (hb : d148736 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d107547 q = 1) (hb : d148610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107547, d148610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107547, d148610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50075 q ha hb
  have h6 (q : Pattern) (ha : d107548 q = 1) (hb : d148611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107548, d148611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107548, d148611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107549 q = 1) (hb : d148612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107549, d148612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107549, d148612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107550 q = 1) (hb : d148613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107550, d148613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107550, d148613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107551 q = 1) (hb : d148614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107551, d148614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107551, d148614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107666 q = 1) (hb : d148731 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107666, d148731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107666, d148731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50097 q ha hb
  have h11 (q : Pattern) (ha : d107667 q = 1) (hb : d148732 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107667, d148732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107667, d148732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107668 q = 1) (hb : d148733 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107668, d148733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107668, d148733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107669 q = 1) (hb : d148734 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107669, d148734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107669, d148734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107670 q = 1) (hb : d148735 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107670, d148735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107670, d148735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107671 q = 1) (hb : d148736 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107671, d148736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107671, d148736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro50099 (p : Pattern) (ha : d107674 p = 1) (hb : d148739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107579 q = 1) (hb : d148643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107579, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50080 q ha hb
    | true =>
      simp only [d107579, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107580 q = 1) (hb : d148644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107580, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107580, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107581 q = 1) (hb : d148645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107581, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107581, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107486 q = 1) (hb : d148548 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107486, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50064 q ha hb
    | true =>
      simp only [d107486, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107487 q = 1) (hb : d148549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107487, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107487, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107488 q = 1) (hb : d148550 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107488, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107488, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107582 q = 1) (hb : d148646 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107582, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107582, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107672 q = 1) (hb : d148737 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107672, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107672, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107673 q = 1) (hb : d148738 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107673, d148738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107673, d148738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107674 q = 1) (hb : d148739 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107674, d148739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107674, d148739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50100 (p : Pattern) (ha : d107678 p = 1) (hb : d148743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107486 q = 1) (hb : d148548 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107486, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50064 q ha hb
    | true =>
      simp only [d107486, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107487 q = 1) (hb : d148549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107487, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107487, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107488 q = 1) (hb : d148550 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107488, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107488, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107672 q = 1) (hb : d148737 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107672, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107672, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107677 q = 1) (hb : d148742 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107677, d148742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107677, d148742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107678 q = 1) (hb : d148743 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107678, d148743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107678, d148743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50101 (p : Pattern) (ha : d107684 p = 1) (hb : d148749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d148740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50099 q ha hb
    | true =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d148741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d148746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d148747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107683 q = 1) (hb : d148748 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107683, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107683, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107684 q = 1) (hb : d148749 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107684, d148749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107684, d148749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50102 (p : Pattern) (ha : d107688 p = 1) (hb : d148753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d148750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107686 q = 1) (hb : d148751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107686, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107686, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107687 q = 1) (hb : d148752 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107687, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107687, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107688 q = 1) (hb : d148753 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107688, d148753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107688, d148753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50103 (p : Pattern) (ha : d107694 p = 1) (hb : d148759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107689 q = 1) (hb : d148754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50101 q ha hb
    | true =>
      simp only [d107689, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50102 q ha hb
  have h2 (q : Pattern) (ha : d107690 q = 1) (hb : d148755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107690, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107690, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107691 q = 1) (hb : d148756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107691, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107691, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107692 q = 1) (hb : d148757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107692, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107692, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107693 q = 1) (hb : d148758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107693, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107693, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107694 q = 1) (hb : d148759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107694, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107694, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50104 (p : Pattern) (ha : d107697 p = 1) (hb : d148762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d148740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50099 q ha hb
    | true =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d148741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d148746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d148747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107683 q = 1) (hb : d148748 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107683, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107683, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107697 q = 1) (hb : d148762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107697, d148762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107697, d148762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50105 (p : Pattern) (ha : d107698 p = 1) (hb : d148763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d148750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107686 q = 1) (hb : d148751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107686, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107686, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107687 q = 1) (hb : d148752 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107687, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107687, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107698 q = 1) (hb : d148763 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107698, d148763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107698, d148763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50106 (p : Pattern) (ha : d107704 p = 1) (hb : d148769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107689 q = 1) (hb : d148754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50101 q ha hb
    | true =>
      simp only [d107689, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50102 q ha hb
  have h2 (q : Pattern) (ha : d107690 q = 1) (hb : d148755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107690, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107690, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107691 q = 1) (hb : d148756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107691, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107691, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107692 q = 1) (hb : d148757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107692, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107692, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107693 q = 1) (hb : d148758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107693, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107693, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107699 q = 1) (hb : d148764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107699, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50104 q ha hb
    | true =>
      simp only [d107699, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50105 q ha hb
  have h7 (q : Pattern) (ha : d107700 q = 1) (hb : d148765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107700, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107700, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107701 q = 1) (hb : d148766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107701, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107701, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107702 q = 1) (hb : d148767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107702, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107702, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107703 q = 1) (hb : d148768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107703, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107703, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107704 q = 1) (hb : d148769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107704, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107704, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50107 (p : Pattern) (ha : d107709 p = 1) (hb : d148774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d148740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50099 q ha hb
    | true =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d148741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d148746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d148747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107708 q = 1) (hb : d148773 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107708, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107708, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107709 q = 1) (hb : d148774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107709, d148774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107709, d148774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50108 (p : Pattern) (ha : d107711 p = 1) (hb : d148776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d148750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107686 q = 1) (hb : d148751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107686, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107686, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107710 q = 1) (hb : d148775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107710, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107710, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107711 q = 1) (hb : d148776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107711, d148776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107711, d148776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50109 (p : Pattern) (ha : d107718 p = 1) (hb : d148783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d148740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50099 q ha hb
    | true =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d148741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d148746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107716 q = 1) (hb : d148781 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107716, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107716, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107717 q = 1) (hb : d148782 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107717, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107717, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107718 q = 1) (hb : d148783 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107718, d148783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107718, d148783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50110 (p : Pattern) (ha : d107721 p = 1) (hb : d148786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d148750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107719 q = 1) (hb : d148784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107719, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107719, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107720 q = 1) (hb : d148785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107720, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107720, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107721 q = 1) (hb : d148786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107721, d148786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107721, d148786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50111 (p : Pattern) (ha : d52295 p = 1) (hb : d148790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21183 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
    | true =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21184 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21185 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21186 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21186, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20992 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20993 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21187 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21187, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21187, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52295 q = 1) (hb : d148790 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52295, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52295, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50112 (p : Pattern) (ha : d107730 p = 1) (hb : d148796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107725 q = 1) (hb : d148791 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107725, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50111 q ha hb
    | true =>
      simp only [d107725, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107726 q = 1) (hb : d148792 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107726, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107726, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107727 q = 1) (hb : d148793 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107727, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107727, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107579 q = 1) (hb : d148643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107579, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50080 q ha hb
    | true =>
      simp only [d107579, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107580 q = 1) (hb : d148644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107580, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107580, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107581 q = 1) (hb : d148645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107581, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107581, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107728 q = 1) (hb : d148794 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107728, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107728, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107486 q = 1) (hb : d148548 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107486, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50064 q ha hb
    | true =>
      simp only [d107486, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107487 q = 1) (hb : d148549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107487, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107487, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107488 q = 1) (hb : d148550 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107488, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107488, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107582 q = 1) (hb : d148646 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107582, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107582, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107729 q = 1) (hb : d148795 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107729, d148795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107729, d148795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107730 q = 1) (hb : d148796 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107730, d148796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107730, d148796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50113 (p : Pattern) (ha : d107736 p = 1) (hb : d148802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107731 q = 1) (hb : d148797 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107731, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50112 q ha hb
    | true =>
      simp only [d107731, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107732 q = 1) (hb : d148798 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107732, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107732, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107675 q = 1) (hb : d148740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50099 q ha hb
    | true =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107676 q = 1) (hb : d148741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107733 q = 1) (hb : d148799 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107733, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107733, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107734 q = 1) (hb : d148800 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107734, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107734, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107735 q = 1) (hb : d148801 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107735, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107735, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107736 q = 1) (hb : d148802 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107736, d148802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107736, d148802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50114 (p : Pattern) (ha : d107742 p = 1) (hb : d148808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d148740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50099 q ha hb
    | true =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d148741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107739 q = 1) (hb : d148805 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107739, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107739, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107740 q = 1) (hb : d148806 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107740, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107740, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107741 q = 1) (hb : d148807 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107741, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107741, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107742 q = 1) (hb : d148808 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107742, d148808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107742, d148808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50115 (p : Pattern) (ha : d107748 p = 1) (hb : d148814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107712 q = 1) (hb : d148777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107712, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50107 q ha hb
    | true =>
      simp only [d107712, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50108 q ha hb
  have h2 (q : Pattern) (ha : d107713 q = 1) (hb : d148778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107713, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107713, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107714 q = 1) (hb : d148779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107714, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107714, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107715 q = 1) (hb : d148780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107715, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107715, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107722 q = 1) (hb : d148787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107722, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50109 q ha hb
    | true =>
      simp only [d107722, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50110 q ha hb
  have h6 (q : Pattern) (ha : d107723 q = 1) (hb : d148788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107723, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107723, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107724 q = 1) (hb : d148789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107724, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107724, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107737 q = 1) (hb : d148803 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107737, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50113 q ha hb
    | true =>
      simp only [d107737, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50101 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107738 q = 1) (hb : d148804 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107738, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107743 q = 1) (hb : d148809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107743, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50114 q ha hb
    | true =>
      simp only [d107743, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107744 q = 1) (hb : d148810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107744, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107744, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107745 q = 1) (hb : d148811 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107745, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107746 q = 1) (hb : d148812 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107746, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107747 q = 1) (hb : d148813 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107747, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107748 q = 1) (hb : d148814 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107748, d148814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107748, d148814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro50116 (p : Pattern) (ha : d107749 p = 1) (hb : d148815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d148740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50099 q ha hb
    | true =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d148741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d148746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d148747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107708 q = 1) (hb : d148773 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107708, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107708, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107749 q = 1) (hb : d148815 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107749, d148815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107749, d148815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50117 (p : Pattern) (ha : d107750 p = 1) (hb : d148816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d148750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107686 q = 1) (hb : d148751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107686, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107686, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107710 q = 1) (hb : d148775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107710, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107710, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107750 q = 1) (hb : d148816 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107750, d148816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107750, d148816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50118 (p : Pattern) (ha : d107755 p = 1) (hb : d148821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d148740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50099 q ha hb
    | true =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d148741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d148746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107716 q = 1) (hb : d148781 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107716, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107716, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107717 q = 1) (hb : d148782 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107717, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107717, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107755 q = 1) (hb : d148821 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107755, d148821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107755, d148821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50119 (p : Pattern) (ha : d107756 p = 1) (hb : d148822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d148744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50100 q ha hb
    | true =>
      simp only [d107679, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d148745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d148750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107719 q = 1) (hb : d148784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107719, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107719, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107720 q = 1) (hb : d148785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107720, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107720, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107756 q = 1) (hb : d148822 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107756, d148822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107756, d148822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50120 (p : Pattern) (ha : d107760 p = 1) (hb : d148826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107731 q = 1) (hb : d148797 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107731, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50112 q ha hb
    | true =>
      simp only [d107731, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107732 q = 1) (hb : d148798 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107732, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107732, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107675 q = 1) (hb : d148740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50099 q ha hb
    | true =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107676 q = 1) (hb : d148741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107733 q = 1) (hb : d148799 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107733, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107733, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107734 q = 1) (hb : d148800 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107734, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107734, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107735 q = 1) (hb : d148801 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107735, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107735, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107760 q = 1) (hb : d148826 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107760, d148826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107760, d148826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50121 (p : Pattern) (ha : d107763 p = 1) (hb : d148829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d148740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50099 q ha hb
    | true =>
      simp only [d107675, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d148741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107739 q = 1) (hb : d148805 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107739, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107739, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107740 q = 1) (hb : d148806 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107740, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107740, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107741 q = 1) (hb : d148807 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107741, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107741, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107763 q = 1) (hb : d148829 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107763, d148829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107763, d148829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50122 (p : Pattern) (ha : d107769 p = 1) (hb : d148835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107712 q = 1) (hb : d148777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107712, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50107 q ha hb
    | true =>
      simp only [d107712, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50108 q ha hb
  have h2 (q : Pattern) (ha : d107713 q = 1) (hb : d148778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107713, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107713, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107714 q = 1) (hb : d148779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107714, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107714, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107715 q = 1) (hb : d148780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107715, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107715, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107722 q = 1) (hb : d148787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107722, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50109 q ha hb
    | true =>
      simp only [d107722, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50110 q ha hb
  have h6 (q : Pattern) (ha : d107723 q = 1) (hb : d148788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107723, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107723, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107724 q = 1) (hb : d148789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107724, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107724, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107737 q = 1) (hb : d148803 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107737, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50113 q ha hb
    | true =>
      simp only [d107737, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50101 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107738 q = 1) (hb : d148804 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107738, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107743 q = 1) (hb : d148809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107743, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50114 q ha hb
    | true =>
      simp only [d107743, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107744 q = 1) (hb : d148810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107744, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107744, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107745 q = 1) (hb : d148811 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107745, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107746 q = 1) (hb : d148812 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107746, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107747 q = 1) (hb : d148813 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107747, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107751 q = 1) (hb : d148817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107751, d148817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50116 q ha hb
    | true =>
      simp only [d107751, d148817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50117 q ha hb
  have h17 (q : Pattern) (ha : d107752 q = 1) (hb : d148818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107752, d148818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107752, d148818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107753 q = 1) (hb : d148819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107753, d148819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107753, d148819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107754 q = 1) (hb : d148820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107754, d148820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107754, d148820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d107757 q = 1) (hb : d148823 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107757, d148823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50118 q ha hb
    | true =>
      simp only [d107757, d148823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50119 q ha hb
  have h21 (q : Pattern) (ha : d107758 q = 1) (hb : d148824 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107758, d148824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107758, d148824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d107759 q = 1) (hb : d148825 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107759, d148825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107759, d148825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107761 q = 1) (hb : d148827 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107761, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50120 q ha hb
    | true =>
      simp only [d107761, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50104 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d107699 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107762 q = 1) (hb : d148828 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d107762, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d107764 q = 1) (hb : d148830 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107764, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50121 q ha hb
    | true =>
      simp only [d107764, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d107765 q = 1) (hb : d148831 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107765, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d107765, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d107766 q = 1) (hb : d148832 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107766, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d107767 q = 1) (hb : d148833 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107767, d148833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d107767, d148833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107768 q = 1) (hb : d148834 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107768, d148834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107768, d148834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107769 q = 1) (hb : d148835 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107769, d148835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107769, d148835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro50123 (p : Pattern) (ha : d107776 p = 1) (hb : d148842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107689 q = 1) (hb : d148754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50101 q ha hb
    | true =>
      simp only [d107689, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50102 q ha hb
  have h2 (q : Pattern) (ha : d107690 q = 1) (hb : d148755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107690, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107690, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107691 q = 1) (hb : d148756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107691, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107691, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107692 q = 1) (hb : d148757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107692, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107692, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107693 q = 1) (hb : d148758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107693, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107693, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107771 q = 1) (hb : d148837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107771, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50102 q ha hb
    | true =>
      simp only [d107771, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107772 q = 1) (hb : d148838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107772, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107772, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107773 q = 1) (hb : d148839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107773, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107773, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107774 q = 1) (hb : d148840 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107774, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107774, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107775 q = 1) (hb : d148841 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107775, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107775, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107776 q = 1) (hb : d148842 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107776, d148842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107776, d148842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50124 (p : Pattern) (ha : d107782 p = 1) (hb : d148848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107771 q = 1) (hb : d148837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107771, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50102 q ha hb
    | true =>
      simp only [d107771, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107772 q = 1) (hb : d148838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107772, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107772, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107773 q = 1) (hb : d148839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107773, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107773, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107774 q = 1) (hb : d148840 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107774, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107774, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107775 q = 1) (hb : d148841 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107775, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107775, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107777 q = 1) (hb : d148843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107777, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50105 q ha hb
    | true =>
      simp only [d107777, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107778 q = 1) (hb : d148844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107778, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107778, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107779 q = 1) (hb : d148845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107779, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107779, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107780 q = 1) (hb : d148846 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107780, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107780, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107781 q = 1) (hb : d148847 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107781, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107781, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107782 q = 1) (hb : d148848 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107782, d148848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107782, d148848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50125 (p : Pattern) (ha : d107789 p = 1) (hb : d148855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107761 q = 1) (hb : d148827 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107761, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50120 q ha hb
    | true =>
      simp only [d107761, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50104 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107699 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107762 q = 1) (hb : d148828 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107762, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107764 q = 1) (hb : d148830 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107764, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50121 q ha hb
    | true =>
      simp only [d107764, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107765 q = 1) (hb : d148831 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107765, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107765, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107766 q = 1) (hb : d148832 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107766, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107787 q = 1) (hb : d148853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107787, d148853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107787, d148853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107788 q = 1) (hb : d148854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107788, d148854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107788, d148854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107789 q = 1) (hb : d148855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107789, d148855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107789, d148855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50126 (p : Pattern) (ha : d107791 p = 1) (hb : d148857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107777 q = 1) (hb : d148843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107777, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50105 q ha hb
    | true =>
      simp only [d107777, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107778 q = 1) (hb : d148844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107778, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107778, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107779 q = 1) (hb : d148845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107779, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107779, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107780 q = 1) (hb : d148846 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107780, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107780, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107781 q = 1) (hb : d148847 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107781, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107781, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107791 q = 1) (hb : d148857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107791, d148857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107791, d148857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50127 (p : Pattern) (ha : d52368 p = 1) (hb : d148863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21309 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
  have h2 (q : Pattern) (ha : d21183 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
    | true =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21310 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21310, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21184 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21311 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21311, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21312 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21312, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21071 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
  have h8 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21072 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21073 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21074 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21313 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21313, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21313, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52368 q = 1) (hb : d148863 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52368, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52368, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50128 (p : Pattern) (ha : d107802 p = 1) (hb : d148869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107797 q = 1) (hb : d148864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107797, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50127 q ha hb
    | true =>
      simp only [d107797, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107798 q = 1) (hb : d148865 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107798, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107798, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107799 q = 1) (hb : d148866 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107799, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107799, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107636 q = 1) (hb : d148701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107636, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50092 q ha hb
    | true =>
      simp only [d107636, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107637 q = 1) (hb : d148702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107637, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107637, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107638 q = 1) (hb : d148703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107638, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107638, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107800 q = 1) (hb : d148867 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107800, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107800, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107523 q = 1) (hb : d148586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107523, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50071 q ha hb
    | true =>
      simp only [d107523, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107524 q = 1) (hb : d148587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107524, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107524, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107525 q = 1) (hb : d148588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107525, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107525, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107639 q = 1) (hb : d148704 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107639, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107639, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107801 q = 1) (hb : d148868 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107801, d148868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107801, d148868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107802 q = 1) (hb : d148869 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107802, d148869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107802, d148869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50129 (p : Pattern) (ha : d107807 p = 1) (hb : d148874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107636 q = 1) (hb : d148701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107636, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50092 q ha hb
    | true =>
      simp only [d107636, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107637 q = 1) (hb : d148702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107637, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107637, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107638 q = 1) (hb : d148703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107638, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107638, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107523 q = 1) (hb : d148586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107523, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50071 q ha hb
    | true =>
      simp only [d107523, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107524 q = 1) (hb : d148587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107524, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107524, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107525 q = 1) (hb : d148588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107525, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107525, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107639 q = 1) (hb : d148704 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107639, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107639, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107805 q = 1) (hb : d148872 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107805, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107805, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107806 q = 1) (hb : d148873 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107806, d148873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107806, d148873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107807 q = 1) (hb : d148874 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107807, d148874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107807, d148874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50130 (p : Pattern) (ha : d107813 p = 1) (hb : d148880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107803 q = 1) (hb : d148870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107803, d148870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50128 q ha hb
    | true =>
      simp only [d107803, d148870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107804 q = 1) (hb : d148871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107804, d148871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107804, d148871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107808 q = 1) (hb : d148875 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107808, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50129 q ha hb
    | true =>
      simp only [d107808, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107809 q = 1) (hb : d148876 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107809, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107809, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107810 q = 1) (hb : d148877 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107810, d148877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107810, d148877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107811 q = 1) (hb : d148878 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107811, d148878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107811, d148878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107812 q = 1) (hb : d148879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107812, d148879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107812, d148879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107813 q = 1) (hb : d148880 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107813, d148880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107813, d148880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50131 (p : Pattern) (ha : d107815 p = 1) (hb : d148882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107523 q = 1) (hb : d148586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107523, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50071 q ha hb
    | true =>
      simp only [d107523, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107524 q = 1) (hb : d148587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107524, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107524, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107525 q = 1) (hb : d148588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107525, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107525, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107805 q = 1) (hb : d148872 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107805, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107805, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107814 q = 1) (hb : d148881 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107814, d148881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107814, d148881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107815 q = 1) (hb : d148882 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107815, d148882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107815, d148882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50132 (p : Pattern) (ha : d107821 p = 1) (hb : d148888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107808 q = 1) (hb : d148875 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107808, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50129 q ha hb
    | true =>
      simp only [d107808, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107809 q = 1) (hb : d148876 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107809, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107809, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107816 q = 1) (hb : d148883 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107816, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50131 q ha hb
    | true =>
      simp only [d107816, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107817 q = 1) (hb : d148884 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107817, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107817, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107818 q = 1) (hb : d148885 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107818, d148885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107818, d148885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107819 q = 1) (hb : d148886 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107819, d148886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107819, d148886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107820 q = 1) (hb : d148887 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107820, d148887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107820, d148887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107821 q = 1) (hb : d148888 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107821, d148888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107821, d148888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50133 (p : Pattern) (ha : d107832 p = 1) (hb : d148894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107808 q = 1) (hb : d148875 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107808, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50129 q ha hb
    | true =>
      simp only [d107808, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107809 q = 1) (hb : d148876 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107809, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107809, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107829 q = 1) (hb : d148891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107829, d148891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107829, d148891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107830 q = 1) (hb : d148892 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107830, d148892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107830, d148892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107831 q = 1) (hb : d148893 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107831, d148893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107831, d148893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107832 q = 1) (hb : d148894 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107832, d148894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107832, d148894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50134 (p : Pattern) (ha : d107838 p = 1) (hb : d148900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107822 q = 1) (hb : d148889 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107822, d148889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50130 q ha hb
    | true =>
      simp only [d107822, d148889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50132 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107827 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107828 q = 1) (hb : d148890 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107828, d148890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107828, d148890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107833 q = 1) (hb : d148895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107833, d148895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50133 q ha hb
    | true =>
      simp only [d107833, d148895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107834 q = 1) (hb : d148896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107834, d148896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107834, d148896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107835 q = 1) (hb : d148897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107835, d148897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107835, d148897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107836 q = 1) (hb : d148898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107836, d148898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107836, d148898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107837 q = 1) (hb : d148899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107837, d148899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107837, d148899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107838 q = 1) (hb : d148900 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107838, d148900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107838, d148900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50135 (p : Pattern) (ha : d107826 p = 1) (hb : d148905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107816 q = 1) (hb : d148883 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107816, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50131 q ha hb
    | true =>
      simp only [d107816, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107817 q = 1) (hb : d148884 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107817, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107817, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107823 q = 1) (hb : d148902 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107823, d148902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107823, d148902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107824 q = 1) (hb : d148903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107824, d148903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107824, d148903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107825 q = 1) (hb : d148904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107825, d148904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107825, d148904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107826 q = 1) (hb : d148905 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107826, d148905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107826, d148905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50136 (p : Pattern) (ha : d107845 p = 1) (hb : d148911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107840 q = 1) (hb : d148906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107840, d148906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50135 q ha hb
    | true =>
      simp only [d107840, d148906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107841 q = 1) (hb : d148907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107841, d148907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107841, d148907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107842 q = 1) (hb : d148908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107842, d148908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107842, d148908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107843 q = 1) (hb : d148909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107843, d148909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107843, d148909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107844 q = 1) (hb : d148910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107844, d148910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107844, d148910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107845 q = 1) (hb : d148911 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107845, d148911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107845, d148911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50137 (p : Pattern) (ha : d107851 p = 1) (hb : d148917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107695 q = 1) (hb : d148760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107695, d148760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107695, d148760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50103 q ha hb
  have h2 (q : Pattern) (ha : d107696 q = 1) (hb : d148761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107696, d148761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107696, d148761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107705 q = 1) (hb : d148770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107705, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50103 q ha hb
    | true =>
      simp only [d107705, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50106 q ha hb
  have h4 (q : Pattern) (ha : d107706 q = 1) (hb : d148771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107706, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107706, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107707 q = 1) (hb : d148772 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107707, d148772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107707, d148772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107770 q = 1) (hb : d148836 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107770, d148836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50115 q ha hb
    | true =>
      simp only [d107770, d148836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50122 q ha hb
  have h7 (q : Pattern) (ha : d107783 q = 1) (hb : d148849 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107783, d148849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50123 q ha hb
    | true =>
      simp only [d107783, d148849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50124 q ha hb
  have h8 (q : Pattern) (ha : d107784 q = 1) (hb : d148850 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107784, d148850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107784, d148850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107785 q = 1) (hb : d148851 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107785, d148851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107785, d148851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107786 q = 1) (hb : d148852 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107786, d148852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107786, d148852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107790 q = 1) (hb : d148856 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107790, d148856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107790, d148856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50125 q ha hb
  have h12 (q : Pattern) (ha : d107792 q = 1) (hb : d148858 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107792, d148858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107792, d148858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50126 q ha hb
  have h13 (q : Pattern) (ha : d107793 q = 1) (hb : d148859 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107793, d148859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107793, d148859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107794 q = 1) (hb : d148860 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107794, d148860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107794, d148860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107795 q = 1) (hb : d148861 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107795, d148861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107795, d148861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107796 q = 1) (hb : d148862 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107796, d148862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107796, d148862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107839 q = 1) (hb : d148901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107839, d148901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107839, d148901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50134 q ha hb
  have h18 (q : Pattern) (ha : d107846 q = 1) (hb : d148912 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107846, d148912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107846, d148912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50136 q ha hb
  have h19 (q : Pattern) (ha : d107847 q = 1) (hb : d148913 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107847, d148913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107847, d148913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d107848 q = 1) (hb : d148914 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107848, d148914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107848, d148914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107849 q = 1) (hb : d148915 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107849, d148915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d107849, d148915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107850 q = 1) (hb : d148916 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107850, d148916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107850, d148916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107851 q = 1) (hb : d148917 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107851, d148917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107851, d148917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro50138 (p : Pattern) (ha : d107857 p = 1) (hb : d148923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107852 q = 1) (hb : d148918 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107852, d148918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107852, d148918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50137 q ha hb
  have h2 (q : Pattern) (ha : d107853 q = 1) (hb : d148919 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107853, d148919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107853, d148919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107854 q = 1) (hb : d148920 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107854, d148920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107854, d148920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107855 q = 1) (hb : d148921 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107855, d148921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107855, d148921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107856 q = 1) (hb : d148922 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107856, d148922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107856, d148922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107857 q = 1) (hb : d148923 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107857, d148923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107857, d148923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50139 (p : Pattern) (ha : d52433 p = 1) (hb : d148790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21183 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
    | true =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21184 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21185 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21186 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21186, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20992 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20993 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21187 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21187, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21187, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52433 q = 1) (hb : d148790 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52433, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52433, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50140 (p : Pattern) (ha : d52435 p = 1) (hb : d148642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20994 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20994, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52435 q = 1) (hb : d148642 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52435, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52435, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50141 (p : Pattern) (ha : d107868 p = 1) (hb : d148927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107859 q = 1) (hb : d148791 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107859, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50139 q ha hb
    | true =>
      simp only [d107859, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107860 q = 1) (hb : d148792 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107860, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107860, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107861 q = 1) (hb : d148793 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107861, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107861, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107862 q = 1) (hb : d148643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107862, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50140 q ha hb
    | true =>
      simp only [d107862, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107863 q = 1) (hb : d148644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107863, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107863, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107864 q = 1) (hb : d148645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107864, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107864, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107865 q = 1) (hb : d148794 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107865, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107865, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107866 q = 1) (hb : d148925 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107866, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107866, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107867 q = 1) (hb : d148926 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107867, d148926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107867, d148926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107868 q = 1) (hb : d148927 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107868, d148927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107868, d148927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50142 (p : Pattern) (ha : d107872 p = 1) (hb : d148931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107862 q = 1) (hb : d148643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107862, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50140 q ha hb
    | true =>
      simp only [d107862, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107863 q = 1) (hb : d148644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107863, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107863, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107864 q = 1) (hb : d148645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107864, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107864, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107866 q = 1) (hb : d148925 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107866, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107866, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107871 q = 1) (hb : d148930 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107871, d148930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107871, d148930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107872 q = 1) (hb : d148931 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107872, d148931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107872, d148931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50143 (p : Pattern) (ha : d107878 p = 1) (hb : d148937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d148928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50141 q ha hb
    | true =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d148929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d148934 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d148935 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107877 q = 1) (hb : d148936 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107877, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107877, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107878 q = 1) (hb : d148937 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107878, d148937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107878, d148937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50144 (p : Pattern) (ha : d107882 p = 1) (hb : d148941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d148938 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107880 q = 1) (hb : d148939 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107880, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107880, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107881 q = 1) (hb : d148940 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107881, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107881, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107882 q = 1) (hb : d148941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107882, d148941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107882, d148941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50145 (p : Pattern) (ha : d107888 p = 1) (hb : d148947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107883 q = 1) (hb : d148942 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50143 q ha hb
    | true =>
      simp only [d107883, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50144 q ha hb
  have h2 (q : Pattern) (ha : d107884 q = 1) (hb : d148943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107884, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107884, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107885 q = 1) (hb : d148944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107885, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107885, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107886 q = 1) (hb : d148945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107886, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107886, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107887 q = 1) (hb : d148946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107887, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107887, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107888 q = 1) (hb : d148947 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107888, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107888, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50146 (p : Pattern) (ha : d107891 p = 1) (hb : d148950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d148928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50141 q ha hb
    | true =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d148929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d148934 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d148935 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107877 q = 1) (hb : d148936 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107877, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107877, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107891 q = 1) (hb : d148950 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107891, d148950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107891, d148950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50147 (p : Pattern) (ha : d107892 p = 1) (hb : d148951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d148938 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107880 q = 1) (hb : d148939 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107880, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107880, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107881 q = 1) (hb : d148940 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107881, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107881, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107892 q = 1) (hb : d148951 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107892, d148951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107892, d148951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50148 (p : Pattern) (ha : d107898 p = 1) (hb : d148957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107883 q = 1) (hb : d148942 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50143 q ha hb
    | true =>
      simp only [d107883, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50144 q ha hb
  have h2 (q : Pattern) (ha : d107884 q = 1) (hb : d148943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107884, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107884, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107885 q = 1) (hb : d148944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107885, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107885, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107886 q = 1) (hb : d148945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107886, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107886, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107887 q = 1) (hb : d148946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107887, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107887, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107893 q = 1) (hb : d148952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107893, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50146 q ha hb
    | true =>
      simp only [d107893, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50147 q ha hb
  have h7 (q : Pattern) (ha : d107894 q = 1) (hb : d148953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107894, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107894, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107895 q = 1) (hb : d148954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107895, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107895, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107896 q = 1) (hb : d148955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107896, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107896, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107897 q = 1) (hb : d148956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107897, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107897, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107898 q = 1) (hb : d148957 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107898, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107898, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50149 (p : Pattern) (ha : d107903 p = 1) (hb : d148962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d148928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50141 q ha hb
    | true =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d148929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d148934 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d148935 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107902 q = 1) (hb : d148961 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107902, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107902, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107903 q = 1) (hb : d148962 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107903, d148962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107903, d148962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50150 (p : Pattern) (ha : d107905 p = 1) (hb : d148964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d148938 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107880 q = 1) (hb : d148939 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107880, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107880, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107904 q = 1) (hb : d148963 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107904, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107904, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107905 q = 1) (hb : d148964 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107905, d148964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107905, d148964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50151 (p : Pattern) (ha : d107912 p = 1) (hb : d148971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d148928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50141 q ha hb
    | true =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d148929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d148934 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107910 q = 1) (hb : d148969 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107910, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107910, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107911 q = 1) (hb : d148970 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107911, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107911, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107912 q = 1) (hb : d148971 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107912, d148971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107912, d148971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50152 (p : Pattern) (ha : d107915 p = 1) (hb : d148974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d148938 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107913 q = 1) (hb : d148972 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107913, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107913, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107914 q = 1) (hb : d148973 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107914, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107914, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107915 q = 1) (hb : d148974 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107915, d148974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107915, d148974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50153 (p : Pattern) (ha : d52516 p = 1) (hb : d148978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21482 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21482, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46113 q ha hb
    | true =>
      simp only [d21482, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21483 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21483, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21483, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21484 q = 1) (hb : d52513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21484, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21484, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21485 q = 1) (hb : d52514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21485, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21485, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21183 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
    | true =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21184 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21185 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21186 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21186, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21486 q = 1) (hb : d52515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21486, d52515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21486, d52515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52516 q = 1) (hb : d148978 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52516, d148978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52516, d148978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50154 (p : Pattern) (ha : d107924 p = 1) (hb : d148984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107919 q = 1) (hb : d148979 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107919, d148979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50153 q ha hb
    | true =>
      simp only [d107919, d148979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107920 q = 1) (hb : d148980 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107920, d148980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107920, d148980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107921 q = 1) (hb : d148981 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107921, d148981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107921, d148981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107859 q = 1) (hb : d148791 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107859, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50139 q ha hb
    | true =>
      simp only [d107859, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107860 q = 1) (hb : d148792 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107860, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107860, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107861 q = 1) (hb : d148793 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107861, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107861, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107922 q = 1) (hb : d148982 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107922, d148982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107922, d148982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107862 q = 1) (hb : d148643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107862, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50140 q ha hb
    | true =>
      simp only [d107862, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107863 q = 1) (hb : d148644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107863, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107863, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107864 q = 1) (hb : d148645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107864, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107864, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107865 q = 1) (hb : d148794 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107865, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107865, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107923 q = 1) (hb : d148983 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107923, d148983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107923, d148983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107924 q = 1) (hb : d148984 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107924, d148984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107924, d148984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50155 (p : Pattern) (ha : d107930 p = 1) (hb : d148990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107925 q = 1) (hb : d148985 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107925, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50154 q ha hb
    | true =>
      simp only [d107925, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107926 q = 1) (hb : d148986 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107926, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107926, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107869 q = 1) (hb : d148928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50141 q ha hb
    | true =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107870 q = 1) (hb : d148929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107927 q = 1) (hb : d148987 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107927, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107927, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107928 q = 1) (hb : d148988 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107928, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107928, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107929 q = 1) (hb : d148989 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107929, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107929, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107930 q = 1) (hb : d148990 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107930, d148990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107930, d148990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50156 (p : Pattern) (ha : d74182 p = 1) (hb : d148642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20994 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20994, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74181 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74182 q = 1) (hb : d148642 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74182, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d74182, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50157 (p : Pattern) (ha : d107938 p = 1) (hb : d148927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107859 q = 1) (hb : d148791 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107859, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50139 q ha hb
    | true =>
      simp only [d107859, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107860 q = 1) (hb : d148792 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107860, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107860, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107861 q = 1) (hb : d148793 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107861, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107861, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107862 q = 1) (hb : d148643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107862, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50140 q ha hb
    | true =>
      simp only [d107862, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107863 q = 1) (hb : d148644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107863, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107863, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107864 q = 1) (hb : d148645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107864, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107864, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107865 q = 1) (hb : d148794 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107865, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107865, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107933 q = 1) (hb : d148643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107933, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50156 q ha hb
    | true =>
      simp only [d107933, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107934 q = 1) (hb : d148644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107934, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107934, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107935 q = 1) (hb : d148645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107935, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107935, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107936 q = 1) (hb : d148925 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107936, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107936, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107937 q = 1) (hb : d148926 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107937, d148926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107937, d148926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107938 q = 1) (hb : d148927 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107938, d148927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107938, d148927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50158 (p : Pattern) (ha : d107944 p = 1) (hb : d148996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107939 q = 1) (hb : d148928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107939, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50157 q ha hb
    | true =>
      simp only [d107939, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107940 q = 1) (hb : d148929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107940, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107940, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107941 q = 1) (hb : d148993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107941, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107941, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107942 q = 1) (hb : d148994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107942, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107942, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107943 q = 1) (hb : d148995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107943, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107943, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107944 q = 1) (hb : d148996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107944, d148996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107944, d148996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50159 (p : Pattern) (ha : d107950 p = 1) (hb : d149002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107906 q = 1) (hb : d148965 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107906, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50149 q ha hb
    | true =>
      simp only [d107906, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50150 q ha hb
  have h2 (q : Pattern) (ha : d107907 q = 1) (hb : d148966 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107907, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107907, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107908 q = 1) (hb : d148967 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107908, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107908, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107909 q = 1) (hb : d148968 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107909, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107909, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107916 q = 1) (hb : d148975 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107916, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50151 q ha hb
    | true =>
      simp only [d107916, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50152 q ha hb
  have h6 (q : Pattern) (ha : d107917 q = 1) (hb : d148976 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107917, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107917, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107918 q = 1) (hb : d148977 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107918, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107918, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107931 q = 1) (hb : d148991 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107931, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50155 q ha hb
    | true =>
      simp only [d107931, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50143 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107883 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107932 q = 1) (hb : d148992 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107932, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107945 q = 1) (hb : d148997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107945, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50158 q ha hb
    | true =>
      simp only [d107945, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107946 q = 1) (hb : d148998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107946, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107946, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107947 q = 1) (hb : d148999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107947, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107948 q = 1) (hb : d149000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107948, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107949 q = 1) (hb : d149001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107949, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107950 q = 1) (hb : d149002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107950, d149002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107950, d149002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro50160 (p : Pattern) (ha : d107951 p = 1) (hb : d149003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d148928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50141 q ha hb
    | true =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d148929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d148934 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d148935 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107902 q = 1) (hb : d148961 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107902, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107902, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107951 q = 1) (hb : d149003 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107951, d149003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107951, d149003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50161 (p : Pattern) (ha : d107952 p = 1) (hb : d149004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d148938 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107880 q = 1) (hb : d148939 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107880, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107880, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107904 q = 1) (hb : d148963 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107904, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107904, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107952 q = 1) (hb : d149004 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107952, d149004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107952, d149004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50162 (p : Pattern) (ha : d107957 p = 1) (hb : d149009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d148928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50141 q ha hb
    | true =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d148929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d148934 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107910 q = 1) (hb : d148969 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107910, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107910, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107911 q = 1) (hb : d148970 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107911, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107911, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107957 q = 1) (hb : d149009 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107957, d149009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107957, d149009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50163 (p : Pattern) (ha : d107958 p = 1) (hb : d149010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d148932 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50142 q ha hb
    | true =>
      simp only [d107873, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d148933 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d148938 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107913 q = 1) (hb : d148972 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107913, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107913, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107914 q = 1) (hb : d148973 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107914, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107914, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107958 q = 1) (hb : d149010 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107958, d149010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107958, d149010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50164 (p : Pattern) (ha : d107962 p = 1) (hb : d149014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107925 q = 1) (hb : d148985 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107925, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50154 q ha hb
    | true =>
      simp only [d107925, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107926 q = 1) (hb : d148986 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107926, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107926, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107869 q = 1) (hb : d148928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50141 q ha hb
    | true =>
      simp only [d107869, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107870 q = 1) (hb : d148929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107927 q = 1) (hb : d148987 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107927, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107927, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107928 q = 1) (hb : d148988 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107928, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107928, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107929 q = 1) (hb : d148989 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107929, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107929, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107962 q = 1) (hb : d149014 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107962, d149014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107962, d149014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50165 (p : Pattern) (ha : d107965 p = 1) (hb : d149017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107939 q = 1) (hb : d148928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107939, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50157 q ha hb
    | true =>
      simp only [d107939, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107940 q = 1) (hb : d148929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107940, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107940, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107941 q = 1) (hb : d148993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107941, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107941, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107942 q = 1) (hb : d148994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107942, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107942, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107943 q = 1) (hb : d148995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107943, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107943, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107965 q = 1) (hb : d149017 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107965, d149017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107965, d149017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50166 (p : Pattern) (ha : d107971 p = 1) (hb : d149023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107906 q = 1) (hb : d148965 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107906, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50149 q ha hb
    | true =>
      simp only [d107906, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50150 q ha hb
  have h2 (q : Pattern) (ha : d107907 q = 1) (hb : d148966 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107907, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107907, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107908 q = 1) (hb : d148967 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107908, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107908, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107909 q = 1) (hb : d148968 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107909, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107909, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107916 q = 1) (hb : d148975 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107916, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50151 q ha hb
    | true =>
      simp only [d107916, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50152 q ha hb
  have h6 (q : Pattern) (ha : d107917 q = 1) (hb : d148976 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107917, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107917, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107918 q = 1) (hb : d148977 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107918, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107918, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107931 q = 1) (hb : d148991 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107931, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50155 q ha hb
    | true =>
      simp only [d107931, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50143 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107883 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107932 q = 1) (hb : d148992 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107932, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107945 q = 1) (hb : d148997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107945, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50158 q ha hb
    | true =>
      simp only [d107945, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107946 q = 1) (hb : d148998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107946, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107946, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107947 q = 1) (hb : d148999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107947, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107948 q = 1) (hb : d149000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107948, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107949 q = 1) (hb : d149001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107949, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107953 q = 1) (hb : d149005 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107953, d149005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50160 q ha hb
    | true =>
      simp only [d107953, d149005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50161 q ha hb
  have h17 (q : Pattern) (ha : d107954 q = 1) (hb : d149006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107954, d149006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107954, d149006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107955 q = 1) (hb : d149007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107955, d149007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107955, d149007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107956 q = 1) (hb : d149008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107956, d149008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107956, d149008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d107959 q = 1) (hb : d149011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107959, d149011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50162 q ha hb
    | true =>
      simp only [d107959, d149011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50163 q ha hb
  have h21 (q : Pattern) (ha : d107960 q = 1) (hb : d149012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107960, d149012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107960, d149012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d107961 q = 1) (hb : d149013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107961, d149013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107961, d149013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107963 q = 1) (hb : d149015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107963, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50164 q ha hb
    | true =>
      simp only [d107963, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50146 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d107893 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107964 q = 1) (hb : d149016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d107964, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d107966 q = 1) (hb : d149018 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107966, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50165 q ha hb
    | true =>
      simp only [d107966, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d107967 q = 1) (hb : d149019 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107967, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d107967, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d107968 q = 1) (hb : d149020 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107968, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d107969 q = 1) (hb : d149021 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107969, d149021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d107969, d149021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107970 q = 1) (hb : d149022 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107970, d149022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107970, d149022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107971 q = 1) (hb : d149023 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107971, d149023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107971, d149023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro50167 (p : Pattern) (ha : d107978 p = 1) (hb : d149030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107883 q = 1) (hb : d148942 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50143 q ha hb
    | true =>
      simp only [d107883, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50144 q ha hb
  have h2 (q : Pattern) (ha : d107884 q = 1) (hb : d148943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107884, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107884, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107885 q = 1) (hb : d148944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107885, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107885, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107886 q = 1) (hb : d148945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107886, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107886, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107887 q = 1) (hb : d148946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107887, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107887, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107973 q = 1) (hb : d149025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107973, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50144 q ha hb
    | true =>
      simp only [d107973, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107974 q = 1) (hb : d149026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107974, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107974, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107975 q = 1) (hb : d149027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107975, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107975, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107976 q = 1) (hb : d149028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107976, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107976, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107977 q = 1) (hb : d149029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107977, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107977, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107978 q = 1) (hb : d149030 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107978, d149030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107978, d149030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50168 (p : Pattern) (ha : d107984 p = 1) (hb : d149036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107973 q = 1) (hb : d149025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107973, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50144 q ha hb
    | true =>
      simp only [d107973, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107974 q = 1) (hb : d149026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107974, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107974, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107975 q = 1) (hb : d149027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107975, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107975, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107976 q = 1) (hb : d149028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107976, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107976, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107977 q = 1) (hb : d149029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107977, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107977, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107979 q = 1) (hb : d149031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107979, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50147 q ha hb
    | true =>
      simp only [d107979, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107980 q = 1) (hb : d149032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107980, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107980, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107981 q = 1) (hb : d149033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107981, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107981, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107982 q = 1) (hb : d149034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107982, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107982, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107983 q = 1) (hb : d149035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107983, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107983, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107984 q = 1) (hb : d149036 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107984, d149036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107984, d149036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50169 (p : Pattern) (ha : d107991 p = 1) (hb : d149043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107963 q = 1) (hb : d149015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107963, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50164 q ha hb
    | true =>
      simp only [d107963, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50146 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107893 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107964 q = 1) (hb : d149016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107964, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107966 q = 1) (hb : d149018 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107966, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50165 q ha hb
    | true =>
      simp only [d107966, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107967 q = 1) (hb : d149019 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107967, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107967, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107968 q = 1) (hb : d149020 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107968, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107989 q = 1) (hb : d149041 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107989, d149041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107989, d149041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107990 q = 1) (hb : d149042 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107990, d149042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107990, d149042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107991 q = 1) (hb : d149043 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107991, d149043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107991, d149043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50170 (p : Pattern) (ha : d107993 p = 1) (hb : d149045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107979 q = 1) (hb : d149031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107979, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50147 q ha hb
    | true =>
      simp only [d107979, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107980 q = 1) (hb : d149032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107980, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107980, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107981 q = 1) (hb : d149033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107981, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107981, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107982 q = 1) (hb : d149034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107982, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107982, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107983 q = 1) (hb : d149035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107983, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107983, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107993 q = 1) (hb : d149045 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107993, d149045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107993, d149045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50171 (p : Pattern) (ha : d52589 p = 1) (hb : d149051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21612 q = 1) (hb : d52584 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21612, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21612, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46113 q ha hb
  have h2 (q : Pattern) (ha : d21482 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21482, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46113 q ha hb
    | true =>
      simp only [d21482, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21613 q = 1) (hb : d52585 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21613, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21613, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21483 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21483, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21483, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21614 q = 1) (hb : d52586 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21614, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21614, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21615 q = 1) (hb : d52587 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21615, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21615, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21309 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
  have h8 (q : Pattern) (ha : d21183 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
    | true =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21310 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21310, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21184 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21311 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21311, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21312 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21312, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21616 q = 1) (hb : d52588 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21616, d52588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21616, d52588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52589 q = 1) (hb : d149051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52589, d149051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52589, d149051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50172 (p : Pattern) (ha : d52595 p = 1) (hb : d148863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21309 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
  have h2 (q : Pattern) (ha : d21183 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46068 q ha hb
    | true =>
      simp only [d21183, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21310 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21310, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21184 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21184, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21311 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21311, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21312 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21312, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21071 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
  have h8 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21072 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21073 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21074 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21313 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21313, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21313, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52595 q = 1) (hb : d148863 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52595, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52595, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50173 (p : Pattern) (ha : d52600 p = 1) (hb : d148700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21075 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21075, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52600 q = 1) (hb : d148700 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52600, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52600, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50174 (p : Pattern) (ha : d108011 p = 1) (hb : d149057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107999 q = 1) (hb : d149052 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107999, d149052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50171 q ha hb
    | true =>
      simp only [d107999, d149052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108000 q = 1) (hb : d149053 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108000, d149053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108000, d149053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108001 q = 1) (hb : d149054 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108001, d149054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108001, d149054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108002 q = 1) (hb : d148864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108002, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50172 q ha hb
    | true =>
      simp only [d108002, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108003 q = 1) (hb : d148865 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108003, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108003, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108004 q = 1) (hb : d148866 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108004, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108004, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108005 q = 1) (hb : d149055 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108005, d149055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108005, d149055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108006 q = 1) (hb : d148701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108006, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50173 q ha hb
    | true =>
      simp only [d108006, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108007 q = 1) (hb : d148702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108007, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108007, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108008 q = 1) (hb : d148703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108008, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108008, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108009 q = 1) (hb : d148867 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108009, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108009, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108010 q = 1) (hb : d149056 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108010, d149056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108010, d149056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108011 q = 1) (hb : d149057 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108011, d149057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108011, d149057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50175 (p : Pattern) (ha : d108016 p = 1) (hb : d149062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108002 q = 1) (hb : d148864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108002, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50172 q ha hb
    | true =>
      simp only [d108002, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108003 q = 1) (hb : d148865 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108003, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108003, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108004 q = 1) (hb : d148866 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108004, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108004, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108006 q = 1) (hb : d148701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108006, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50173 q ha hb
    | true =>
      simp only [d108006, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108007 q = 1) (hb : d148702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108007, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108007, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108008 q = 1) (hb : d148703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108008, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108008, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108009 q = 1) (hb : d148867 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108009, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108009, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108014 q = 1) (hb : d149060 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108014, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108014, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108015 q = 1) (hb : d149061 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108015, d149061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108015, d149061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108016 q = 1) (hb : d149062 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108016, d149062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108016, d149062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50176 (p : Pattern) (ha : d108022 p = 1) (hb : d149068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108012 q = 1) (hb : d149058 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108012, d149058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50174 q ha hb
    | true =>
      simp only [d108012, d149058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108013 q = 1) (hb : d149059 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108013, d149059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108013, d149059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108017 q = 1) (hb : d149063 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108017, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50175 q ha hb
    | true =>
      simp only [d108017, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108018 q = 1) (hb : d149064 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108018, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108018, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108019 q = 1) (hb : d149065 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108019, d149065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108019, d149065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108020 q = 1) (hb : d149066 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108020, d149066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108020, d149066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108021 q = 1) (hb : d149067 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108021, d149067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108021, d149067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108022 q = 1) (hb : d149068 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108022, d149068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108022, d149068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50177 (p : Pattern) (ha : d108024 p = 1) (hb : d149070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108006 q = 1) (hb : d148701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108006, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50173 q ha hb
    | true =>
      simp only [d108006, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108007 q = 1) (hb : d148702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108007, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108007, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108008 q = 1) (hb : d148703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108008, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108008, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108014 q = 1) (hb : d149060 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108014, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108014, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108023 q = 1) (hb : d149069 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108023, d149069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108023, d149069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108024 q = 1) (hb : d149070 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108024, d149070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108024, d149070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50178 (p : Pattern) (ha : d108030 p = 1) (hb : d149076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108017 q = 1) (hb : d149063 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108017, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50175 q ha hb
    | true =>
      simp only [d108017, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108018 q = 1) (hb : d149064 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108018, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108018, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108025 q = 1) (hb : d149071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108025, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50177 q ha hb
    | true =>
      simp only [d108025, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108026 q = 1) (hb : d149072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108026, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108026, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108027 q = 1) (hb : d149073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108027, d149073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108027, d149073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108028 q = 1) (hb : d149074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108028, d149074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108028, d149074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108029 q = 1) (hb : d149075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108029, d149075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108029, d149075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108030 q = 1) (hb : d149076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108030, d149076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108030, d149076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50179 (p : Pattern) (ha : d74226 p = 1) (hb : d148700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21075 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21075, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74225 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74226 q = 1) (hb : d148700 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74226, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d74226, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50180 (p : Pattern) (ha : d108043 p = 1) (hb : d149062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108002 q = 1) (hb : d148864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108002, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50172 q ha hb
    | true =>
      simp only [d108002, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108003 q = 1) (hb : d148865 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108003, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108003, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108004 q = 1) (hb : d148866 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108004, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108004, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108006 q = 1) (hb : d148701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108006, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50173 q ha hb
    | true =>
      simp only [d108006, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108007 q = 1) (hb : d148702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108007, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108007, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108008 q = 1) (hb : d148703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108008, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108008, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108009 q = 1) (hb : d148867 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108009, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108009, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108038 q = 1) (hb : d148701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108038, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50179 q ha hb
    | true =>
      simp only [d108038, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108039 q = 1) (hb : d148702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108039, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108039, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108040 q = 1) (hb : d148703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108040, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108040, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108041 q = 1) (hb : d149060 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108041, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108041, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108042 q = 1) (hb : d149061 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108042, d149061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108042, d149061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108043 q = 1) (hb : d149062 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108043, d149062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108043, d149062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50181 (p : Pattern) (ha : d108049 p = 1) (hb : d149082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108044 q = 1) (hb : d149063 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108044, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50180 q ha hb
    | true =>
      simp only [d108044, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108045 q = 1) (hb : d149064 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108045, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108045, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108046 q = 1) (hb : d149079 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108046, d149079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108046, d149079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108047 q = 1) (hb : d149080 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108047, d149080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108047, d149080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108048 q = 1) (hb : d149081 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108048, d149081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108048, d149081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108049 q = 1) (hb : d149082 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108049, d149082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108049, d149082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50182 (p : Pattern) (ha : d108055 p = 1) (hb : d149088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108031 q = 1) (hb : d149077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108031, d149077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50176 q ha hb
    | true =>
      simp only [d108031, d149077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50178 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108036 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108037 q = 1) (hb : d149078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108037, d149078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108037, d149078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108050 q = 1) (hb : d149083 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108050, d149083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50181 q ha hb
    | true =>
      simp only [d108050, d149083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108051 q = 1) (hb : d149084 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108051, d149084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108051, d149084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108052 q = 1) (hb : d149085 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108052, d149085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108052, d149085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108053 q = 1) (hb : d149086 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108053, d149086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108053, d149086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108054 q = 1) (hb : d149087 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108054, d149087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108054, d149087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108055 q = 1) (hb : d149088 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108055, d149088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108055, d149088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50183 (p : Pattern) (ha : d108035 p = 1) (hb : d149093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108025 q = 1) (hb : d149071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108025, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50177 q ha hb
    | true =>
      simp only [d108025, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108026 q = 1) (hb : d149072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108026, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108026, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108032 q = 1) (hb : d149090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108032, d149090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108032, d149090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108033 q = 1) (hb : d149091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108033, d149091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108033, d149091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108034 q = 1) (hb : d149092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108034, d149092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108034, d149092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108035 q = 1) (hb : d149093 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108035, d149093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108035, d149093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50184 (p : Pattern) (ha : d108062 p = 1) (hb : d149099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108057 q = 1) (hb : d149094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108057, d149094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50183 q ha hb
    | true =>
      simp only [d108057, d149094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108058 q = 1) (hb : d149095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108058, d149095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108058, d149095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108059 q = 1) (hb : d149096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108059, d149096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108059, d149096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108060 q = 1) (hb : d149097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108060, d149097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108060, d149097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108061 q = 1) (hb : d149098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108061, d149098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108061, d149098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108062 q = 1) (hb : d149099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108062, d149099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108062, d149099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50185 (p : Pattern) (ha : d108068 p = 1) (hb : d149105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107889 q = 1) (hb : d148948 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107889, d148948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107889, d148948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50145 q ha hb
  have h2 (q : Pattern) (ha : d107890 q = 1) (hb : d148949 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107890, d148949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107890, d148949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107899 q = 1) (hb : d148958 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107899, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50145 q ha hb
    | true =>
      simp only [d107899, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50148 q ha hb
  have h4 (q : Pattern) (ha : d107900 q = 1) (hb : d148959 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107900, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107900, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107901 q = 1) (hb : d148960 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107901, d148960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107901, d148960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107972 q = 1) (hb : d149024 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107972, d149024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50159 q ha hb
    | true =>
      simp only [d107972, d149024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50166 q ha hb
  have h7 (q : Pattern) (ha : d107985 q = 1) (hb : d149037 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107985, d149037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50167 q ha hb
    | true =>
      simp only [d107985, d149037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50168 q ha hb
  have h8 (q : Pattern) (ha : d107986 q = 1) (hb : d149038 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107986, d149038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107986, d149038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107987 q = 1) (hb : d149039 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107987, d149039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107987, d149039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107988 q = 1) (hb : d149040 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107988, d149040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107988, d149040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107992 q = 1) (hb : d149044 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107992, d149044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107992, d149044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50169 q ha hb
  have h12 (q : Pattern) (ha : d107994 q = 1) (hb : d149046 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107994, d149046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107994, d149046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50170 q ha hb
  have h13 (q : Pattern) (ha : d107995 q = 1) (hb : d149047 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107995, d149047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107995, d149047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107996 q = 1) (hb : d149048 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107996, d149048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107996, d149048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107997 q = 1) (hb : d149049 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107997, d149049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107997, d149049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107998 q = 1) (hb : d149050 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107998, d149050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107998, d149050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108056 q = 1) (hb : d149089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108056, d149089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108056, d149089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50182 q ha hb
  have h18 (q : Pattern) (ha : d108063 q = 1) (hb : d149100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108063, d149100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108063, d149100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50184 q ha hb
  have h19 (q : Pattern) (ha : d108064 q = 1) (hb : d149101 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108064, d149101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108064, d149101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108065 q = 1) (hb : d149102 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108065, d149102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108065, d149102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108066 q = 1) (hb : d149103 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108066, d149103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108066, d149103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108067 q = 1) (hb : d149104 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108067, d149104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108067, d149104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108068 q = 1) (hb : d149105 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108068, d149105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108068, d149105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro50186 (p : Pattern) (ha : d108074 p = 1) (hb : d149111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108069 q = 1) (hb : d149106 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108069, d149106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108069, d149106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50185 q ha hb
  have h2 (q : Pattern) (ha : d108070 q = 1) (hb : d149107 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108070, d149107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108070, d149107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108071 q = 1) (hb : d149108 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108071, d149108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108071, d149108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108072 q = 1) (hb : d149109 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108072, d149109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108072, d149109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108073 q = 1) (hb : d149110 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108073, d149110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108073, d149110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108074 q = 1) (hb : d149111 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108074, d149111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108074, d149111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50187 (p : Pattern) (ha : d52707 p = 1) (hb : d149114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21737 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
    | true =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21738 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21739 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21739, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21739, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21740 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21740, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21740, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21742 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
    | true =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21743 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21744 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21744, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21745 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21745, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21746 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21746, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21746, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52707 q = 1) (hb : d149114 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52707, d149114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52707, d149114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50188 (p : Pattern) (ha : d52709 p = 1) (hb : d149118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21742 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
    | true =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21743 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21744 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21744, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21745 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21745, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21755 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33425 q ha hb
    | true =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21756 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21757 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21757, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21758 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21758, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21759 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21759, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21759, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52709 q = 1) (hb : d149118 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52709, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52709, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50189 (p : Pattern) (ha : d108086 p = 1) (hb : d149125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108077 q = 1) (hb : d149115 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108077, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50187 q ha hb
    | true =>
      simp only [d108077, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108078 q = 1) (hb : d149116 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108078, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108078, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108079 q = 1) (hb : d149117 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108079, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108079, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108080 q = 1) (hb : d149119 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108080, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50188 q ha hb
    | true =>
      simp only [d108080, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108081 q = 1) (hb : d149120 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108081, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108081, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108082 q = 1) (hb : d149121 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108082, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108082, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108083 q = 1) (hb : d149122 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108083, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108083, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108084 q = 1) (hb : d149123 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108084, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108084, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108085 q = 1) (hb : d149124 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108085, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108085, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108086 q = 1) (hb : d149125 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108086, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108086, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50190 (p : Pattern) (ha : d108090 p = 1) (hb : d149129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108080 q = 1) (hb : d149119 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108080, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50188 q ha hb
    | true =>
      simp only [d108080, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108081 q = 1) (hb : d149120 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108081, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108081, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108082 q = 1) (hb : d149121 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108082, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108082, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108084 q = 1) (hb : d149123 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108084, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108084, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108089 q = 1) (hb : d149128 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108089, d149128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108089, d149128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108090 q = 1) (hb : d149129 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108090, d149129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108090, d149129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50191 (p : Pattern) (ha : d108096 p = 1) (hb : d149135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d149126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50189 q ha hb
    | true =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d149127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d149132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d149133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108095 q = 1) (hb : d149134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108095, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108095, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108096 q = 1) (hb : d149135 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108096, d149135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108096, d149135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50192 (p : Pattern) (ha : d108100 p = 1) (hb : d149139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d149136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108098 q = 1) (hb : d149137 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108098, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108098, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108099 q = 1) (hb : d149138 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108099, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108099, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108100 q = 1) (hb : d149139 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108100, d149139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108100, d149139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50193 (p : Pattern) (ha : d108106 p = 1) (hb : d149145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108101 q = 1) (hb : d149140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50191 q ha hb
    | true =>
      simp only [d108101, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50192 q ha hb
  have h2 (q : Pattern) (ha : d108102 q = 1) (hb : d149141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108102, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108102, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108103 q = 1) (hb : d149142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108103, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108103, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108104 q = 1) (hb : d149143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108104, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108104, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108105 q = 1) (hb : d149144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108105, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108105, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108106 q = 1) (hb : d149145 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108106, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108106, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50194 (p : Pattern) (ha : d108109 p = 1) (hb : d149148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d149126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50189 q ha hb
    | true =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d149127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d149132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d149133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108095 q = 1) (hb : d149134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108095, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108095, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108109 q = 1) (hb : d149148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108109, d149148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108109, d149148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50195 (p : Pattern) (ha : d108110 p = 1) (hb : d149149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d149136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108098 q = 1) (hb : d149137 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108098, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108098, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108099 q = 1) (hb : d149138 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108099, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108099, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108110 q = 1) (hb : d149149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108110, d149149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108110, d149149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50196 (p : Pattern) (ha : d108116 p = 1) (hb : d149155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108101 q = 1) (hb : d149140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50191 q ha hb
    | true =>
      simp only [d108101, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50192 q ha hb
  have h2 (q : Pattern) (ha : d108102 q = 1) (hb : d149141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108102, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108102, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108103 q = 1) (hb : d149142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108103, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108103, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108104 q = 1) (hb : d149143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108104, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108104, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108105 q = 1) (hb : d149144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108105, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108105, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108111 q = 1) (hb : d149150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108111, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50194 q ha hb
    | true =>
      simp only [d108111, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50195 q ha hb
  have h7 (q : Pattern) (ha : d108112 q = 1) (hb : d149151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108112, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108112, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108113 q = 1) (hb : d149152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108113, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108113, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108114 q = 1) (hb : d149153 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108114, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108114, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108115 q = 1) (hb : d149154 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108115, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108115, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108116 q = 1) (hb : d149155 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108116, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108116, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50197 (p : Pattern) (ha : d108121 p = 1) (hb : d149160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d149126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50189 q ha hb
    | true =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d149127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d149132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d149133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108120 q = 1) (hb : d149159 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108120, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108120, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108121 q = 1) (hb : d149160 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108121, d149160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108121, d149160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50198 (p : Pattern) (ha : d108123 p = 1) (hb : d149162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d149136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108098 q = 1) (hb : d149137 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108098, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108098, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108122 q = 1) (hb : d149161 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108122, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108122, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108123 q = 1) (hb : d149162 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108123, d149162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108123, d149162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50199 (p : Pattern) (ha : d108130 p = 1) (hb : d149169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d149126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50189 q ha hb
    | true =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d149127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d149132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108128 q = 1) (hb : d149167 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108128, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108128, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108129 q = 1) (hb : d149168 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108129, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108129, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108130 q = 1) (hb : d149169 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108130, d149169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108130, d149169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50200 (p : Pattern) (ha : d108133 p = 1) (hb : d149172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d149136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108131 q = 1) (hb : d149170 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108131, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108131, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108132 q = 1) (hb : d149171 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108132, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108132, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108133 q = 1) (hb : d149172 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108133, d149172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108133, d149172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50201 (p : Pattern) (ha : d52796 p = 1) (hb : d149176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21835 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21835, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46165 q ha hb
    | true =>
      simp only [d21835, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21836 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21836, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21836, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21837 q = 1) (hb : d52793 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21837, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21837, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21838 q = 1) (hb : d52794 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21838, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21838, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21737 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
    | true =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21738 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21739 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21739, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21739, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21740 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21740, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21740, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21839 q = 1) (hb : d52795 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21839, d52795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21839, d52795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52796 q = 1) (hb : d149176 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52796, d149176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52796, d149176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50202 (p : Pattern) (ha : d108142 p = 1) (hb : d149182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108137 q = 1) (hb : d149177 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108137, d149177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50201 q ha hb
    | true =>
      simp only [d108137, d149177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108138 q = 1) (hb : d149178 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108138, d149178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108138, d149178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108139 q = 1) (hb : d149179 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108139, d149179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108139, d149179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108077 q = 1) (hb : d149115 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108077, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50187 q ha hb
    | true =>
      simp only [d108077, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108078 q = 1) (hb : d149116 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108078, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108078, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108079 q = 1) (hb : d149117 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108079, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108079, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108140 q = 1) (hb : d149180 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108140, d149180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108140, d149180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108080 q = 1) (hb : d149119 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108080, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50188 q ha hb
    | true =>
      simp only [d108080, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108081 q = 1) (hb : d149120 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108081, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108081, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108082 q = 1) (hb : d149121 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108082, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108082, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108083 q = 1) (hb : d149122 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108083, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108083, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108141 q = 1) (hb : d149181 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108141, d149181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108141, d149181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108142 q = 1) (hb : d149182 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108142, d149182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108142, d149182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50203 (p : Pattern) (ha : d108148 p = 1) (hb : d149188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108143 q = 1) (hb : d149183 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108143, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50202 q ha hb
    | true =>
      simp only [d108143, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108144 q = 1) (hb : d149184 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108144, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108144, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108087 q = 1) (hb : d149126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50189 q ha hb
    | true =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108088 q = 1) (hb : d149127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108145 q = 1) (hb : d149185 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108145, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108145, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108146 q = 1) (hb : d149186 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108146, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108146, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108147 q = 1) (hb : d149187 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108147, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108147, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108148 q = 1) (hb : d149188 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108148, d149188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108148, d149188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50204 (p : Pattern) (ha : d74271 p = 1) (hb : d149118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21742 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
    | true =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21743 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21744 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21744, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21745 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21745, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21755 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33425 q ha hb
    | true =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21756 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21757 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21757, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21758 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21758, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21759 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21759, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21759, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74270 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74271 q = 1) (hb : d149118 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74271, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d74271, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50205 (p : Pattern) (ha : d108156 p = 1) (hb : d149125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108077 q = 1) (hb : d149115 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108077, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50187 q ha hb
    | true =>
      simp only [d108077, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108078 q = 1) (hb : d149116 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108078, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108078, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108079 q = 1) (hb : d149117 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108079, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108079, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108080 q = 1) (hb : d149119 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108080, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50188 q ha hb
    | true =>
      simp only [d108080, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108081 q = 1) (hb : d149120 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108081, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108081, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108082 q = 1) (hb : d149121 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108082, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108082, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108083 q = 1) (hb : d149122 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108083, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108083, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108151 q = 1) (hb : d149119 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108151, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50204 q ha hb
    | true =>
      simp only [d108151, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108152 q = 1) (hb : d149120 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108152, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108152, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108153 q = 1) (hb : d149121 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108153, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108153, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108154 q = 1) (hb : d149123 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108154, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108154, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108155 q = 1) (hb : d149124 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108155, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108155, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108156 q = 1) (hb : d149125 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108156, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108156, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50206 (p : Pattern) (ha : d108162 p = 1) (hb : d149194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108157 q = 1) (hb : d149126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108157, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50205 q ha hb
    | true =>
      simp only [d108157, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108158 q = 1) (hb : d149127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108158, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108158, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108159 q = 1) (hb : d149191 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108159, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108159, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108160 q = 1) (hb : d149192 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108160, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108160, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108161 q = 1) (hb : d149193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108161, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108161, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108162 q = 1) (hb : d149194 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108162, d149194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108162, d149194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50207 (p : Pattern) (ha : d108168 p = 1) (hb : d149200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108124 q = 1) (hb : d149163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108124, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50197 q ha hb
    | true =>
      simp only [d108124, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50198 q ha hb
  have h2 (q : Pattern) (ha : d108125 q = 1) (hb : d149164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108125, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108125, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108126 q = 1) (hb : d149165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108126, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108126, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108127 q = 1) (hb : d149166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108127, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108127, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108134 q = 1) (hb : d149173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108134, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50199 q ha hb
    | true =>
      simp only [d108134, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50200 q ha hb
  have h6 (q : Pattern) (ha : d108135 q = 1) (hb : d149174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108135, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108135, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108136 q = 1) (hb : d149175 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108136, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108136, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108149 q = 1) (hb : d149189 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108149, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50203 q ha hb
    | true =>
      simp only [d108149, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50191 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108101 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108150 q = 1) (hb : d149190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108150, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108163 q = 1) (hb : d149195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108163, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50206 q ha hb
    | true =>
      simp only [d108163, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108164 q = 1) (hb : d149196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108164, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108164, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108165 q = 1) (hb : d149197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108165, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108166 q = 1) (hb : d149198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108166, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108167 q = 1) (hb : d149199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108167, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108168 q = 1) (hb : d149200 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108168, d149200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108168, d149200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro50208 (p : Pattern) (ha : d108169 p = 1) (hb : d149201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d149126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50189 q ha hb
    | true =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d149127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d149132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d149133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108120 q = 1) (hb : d149159 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108120, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108120, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108169 q = 1) (hb : d149201 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108169, d149201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108169, d149201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50209 (p : Pattern) (ha : d108170 p = 1) (hb : d149202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d149136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108098 q = 1) (hb : d149137 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108098, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108098, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108122 q = 1) (hb : d149161 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108122, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108122, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108170 q = 1) (hb : d149202 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108170, d149202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108170, d149202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50210 (p : Pattern) (ha : d108175 p = 1) (hb : d149207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d149126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50189 q ha hb
    | true =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d149127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d149132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108128 q = 1) (hb : d149167 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108128, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108128, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108129 q = 1) (hb : d149168 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108129, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108129, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108175 q = 1) (hb : d149207 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108175, d149207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108175, d149207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50211 (p : Pattern) (ha : d108176 p = 1) (hb : d149208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d149130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50190 q ha hb
    | true =>
      simp only [d108091, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d149131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d149136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108131 q = 1) (hb : d149170 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108131, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108131, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108132 q = 1) (hb : d149171 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108132, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108132, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108176 q = 1) (hb : d149208 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108176, d149208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108176, d149208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50212 (p : Pattern) (ha : d108180 p = 1) (hb : d149212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108143 q = 1) (hb : d149183 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108143, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50202 q ha hb
    | true =>
      simp only [d108143, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108144 q = 1) (hb : d149184 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108144, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108144, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108087 q = 1) (hb : d149126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50189 q ha hb
    | true =>
      simp only [d108087, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108088 q = 1) (hb : d149127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108145 q = 1) (hb : d149185 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108145, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108145, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108146 q = 1) (hb : d149186 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108146, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108146, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108147 q = 1) (hb : d149187 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108147, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108147, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108180 q = 1) (hb : d149212 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108180, d149212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108180, d149212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50213 (p : Pattern) (ha : d108183 p = 1) (hb : d149215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108157 q = 1) (hb : d149126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108157, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50205 q ha hb
    | true =>
      simp only [d108157, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108158 q = 1) (hb : d149127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108158, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108158, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108159 q = 1) (hb : d149191 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108159, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108159, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108160 q = 1) (hb : d149192 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108160, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108160, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108161 q = 1) (hb : d149193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108161, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108161, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108183 q = 1) (hb : d149215 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108183, d149215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108183, d149215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50214 (p : Pattern) (ha : d108189 p = 1) (hb : d149221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108124 q = 1) (hb : d149163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108124, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50197 q ha hb
    | true =>
      simp only [d108124, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50198 q ha hb
  have h2 (q : Pattern) (ha : d108125 q = 1) (hb : d149164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108125, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108125, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108126 q = 1) (hb : d149165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108126, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108126, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108127 q = 1) (hb : d149166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108127, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108127, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108134 q = 1) (hb : d149173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108134, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50199 q ha hb
    | true =>
      simp only [d108134, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50200 q ha hb
  have h6 (q : Pattern) (ha : d108135 q = 1) (hb : d149174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108135, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108135, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108136 q = 1) (hb : d149175 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108136, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108136, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108149 q = 1) (hb : d149189 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108149, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50203 q ha hb
    | true =>
      simp only [d108149, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50191 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108101 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108150 q = 1) (hb : d149190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108150, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108163 q = 1) (hb : d149195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108163, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50206 q ha hb
    | true =>
      simp only [d108163, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108164 q = 1) (hb : d149196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108164, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108164, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108165 q = 1) (hb : d149197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108165, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108166 q = 1) (hb : d149198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108166, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108167 q = 1) (hb : d149199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108167, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108171 q = 1) (hb : d149203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108171, d149203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50208 q ha hb
    | true =>
      simp only [d108171, d149203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50209 q ha hb
  have h17 (q : Pattern) (ha : d108172 q = 1) (hb : d149204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108172, d149204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108172, d149204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108173 q = 1) (hb : d149205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108173, d149205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108173, d149205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d108174 q = 1) (hb : d149206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108174, d149206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108174, d149206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108177 q = 1) (hb : d149209 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108177, d149209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50210 q ha hb
    | true =>
      simp only [d108177, d149209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50211 q ha hb
  have h21 (q : Pattern) (ha : d108178 q = 1) (hb : d149210 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108178, d149210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108178, d149210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d108179 q = 1) (hb : d149211 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108179, d149211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108179, d149211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108181 q = 1) (hb : d149213 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108181, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50212 q ha hb
    | true =>
      simp only [d108181, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50194 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d108111 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d108182 q = 1) (hb : d149214 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108182, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d108184 q = 1) (hb : d149216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108184, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50213 q ha hb
    | true =>
      simp only [d108184, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d108185 q = 1) (hb : d149217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108185, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108185, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d108186 q = 1) (hb : d149218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108186, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108187 q = 1) (hb : d149219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108187, d149219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108187, d149219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d108188 q = 1) (hb : d149220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108188, d149220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108188, d149220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108189 q = 1) (hb : d149221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108189, d149221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108189, d149221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro50215 (p : Pattern) (ha : d108196 p = 1) (hb : d149228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108101 q = 1) (hb : d149140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50191 q ha hb
    | true =>
      simp only [d108101, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50192 q ha hb
  have h2 (q : Pattern) (ha : d108102 q = 1) (hb : d149141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108102, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108102, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108103 q = 1) (hb : d149142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108103, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108103, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108104 q = 1) (hb : d149143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108104, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108104, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108105 q = 1) (hb : d149144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108105, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108105, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108191 q = 1) (hb : d149223 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108191, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50192 q ha hb
    | true =>
      simp only [d108191, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108192 q = 1) (hb : d149224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108192, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108192, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108193 q = 1) (hb : d149225 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108193, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108193, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108194 q = 1) (hb : d149226 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108194, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108194, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108195 q = 1) (hb : d149227 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108195, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108195, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108196 q = 1) (hb : d149228 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108196, d149228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108196, d149228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50216 (p : Pattern) (ha : d108202 p = 1) (hb : d149234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108191 q = 1) (hb : d149223 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108191, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50192 q ha hb
    | true =>
      simp only [d108191, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108192 q = 1) (hb : d149224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108192, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108192, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108193 q = 1) (hb : d149225 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108193, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108193, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108194 q = 1) (hb : d149226 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108194, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108194, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108195 q = 1) (hb : d149227 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108195, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108195, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108197 q = 1) (hb : d149229 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108197, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50195 q ha hb
    | true =>
      simp only [d108197, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108198 q = 1) (hb : d149230 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108198, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108198, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108199 q = 1) (hb : d149231 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108199, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108199, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108200 q = 1) (hb : d149232 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108200, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108200, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108201 q = 1) (hb : d149233 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108201, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108201, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108202 q = 1) (hb : d149234 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108202, d149234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108202, d149234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50217 (p : Pattern) (ha : d108209 p = 1) (hb : d149241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108181 q = 1) (hb : d149213 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108181, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50212 q ha hb
    | true =>
      simp only [d108181, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50194 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108111 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108182 q = 1) (hb : d149214 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108182, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108184 q = 1) (hb : d149216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108184, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50213 q ha hb
    | true =>
      simp only [d108184, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108185 q = 1) (hb : d149217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108185, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108185, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108186 q = 1) (hb : d149218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108186, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108207 q = 1) (hb : d149239 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108207, d149239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108207, d149239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108208 q = 1) (hb : d149240 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108208, d149240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108208, d149240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108209 q = 1) (hb : d149241 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108209, d149241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108209, d149241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50218 (p : Pattern) (ha : d108211 p = 1) (hb : d149243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108197 q = 1) (hb : d149229 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108197, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50195 q ha hb
    | true =>
      simp only [d108197, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108198 q = 1) (hb : d149230 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108198, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108198, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108199 q = 1) (hb : d149231 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108199, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108199, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108200 q = 1) (hb : d149232 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108200, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108200, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108201 q = 1) (hb : d149233 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108201, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108201, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108211 q = 1) (hb : d149243 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108211, d149243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108211, d149243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50219 (p : Pattern) (ha : d52878 p = 1) (hb : d149249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22024 q = 1) (hb : d52864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22024, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22024, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46165 q ha hb
  have h2 (q : Pattern) (ha : d21835 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21835, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46165 q ha hb
    | true =>
      simp only [d21835, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22025 q = 1) (hb : d52865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22025, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22025, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21836 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21836, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21836, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22026 q = 1) (hb : d52866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22026, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22026, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22027 q = 1) (hb : d52867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22027, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22027, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22028 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22028, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22028, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
  have h8 (q : Pattern) (ha : d21737 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
    | true =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22029 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22029, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22029, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21738 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22030 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22030, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22030, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22031 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22031, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22031, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22032 q = 1) (hb : d52872 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22032, d52872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22032, d52872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52878 q = 1) (hb : d149249 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52878, d149249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52878, d149249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50220 (p : Pattern) (ha : d52884 p = 1) (hb : d149253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22028 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22028, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22028, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
  have h2 (q : Pattern) (ha : d21737 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
    | true =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22029 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22029, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22029, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21738 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22030 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22030, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22030, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22031 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22031, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22031, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22043 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22043, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22043, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
  have h8 (q : Pattern) (ha : d21742 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
    | true =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22044 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22044, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22044, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21743 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22045 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22045, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22045, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22046 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22046, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22046, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22047 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22047, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22047, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52884 q = 1) (hb : d149253 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52884, d149253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52884, d149253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50221 (p : Pattern) (ha : d52889 p = 1) (hb : d149258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22043 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22043, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22043, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
  have h2 (q : Pattern) (ha : d21742 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
    | true =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22044 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22044, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22044, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21743 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22045 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22045, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22045, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22046 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22046, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22046, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22064 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22064, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22064, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33425 q ha hb
  have h8 (q : Pattern) (ha : d21755 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33425 q ha hb
    | true =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22065 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22065, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22065, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21756 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22066 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22066, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22066, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22067 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22067, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22067, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22068 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22068, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22068, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52889 q = 1) (hb : d149258 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52889, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52889, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50222 (p : Pattern) (ha : d108229 p = 1) (hb : d149264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108217 q = 1) (hb : d149250 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108217, d149250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50219 q ha hb
    | true =>
      simp only [d108217, d149250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108218 q = 1) (hb : d149251 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108218, d149251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108218, d149251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108219 q = 1) (hb : d149252 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108219, d149252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108219, d149252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108220 q = 1) (hb : d149254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108220, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50220 q ha hb
    | true =>
      simp only [d108220, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108221 q = 1) (hb : d149255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108221, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108221, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108222 q = 1) (hb : d149256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108222, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108222, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108223 q = 1) (hb : d149257 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108223, d149257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108223, d149257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108224 q = 1) (hb : d149259 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108224, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50221 q ha hb
    | true =>
      simp only [d108224, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108225 q = 1) (hb : d149260 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108225, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108225, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108226 q = 1) (hb : d149261 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108226, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108226, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108227 q = 1) (hb : d149262 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108227, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108227, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108228 q = 1) (hb : d149263 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108228, d149263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108228, d149263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108229 q = 1) (hb : d149264 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108229, d149264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108229, d149264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50223 (p : Pattern) (ha : d108234 p = 1) (hb : d149269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108220 q = 1) (hb : d149254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108220, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50220 q ha hb
    | true =>
      simp only [d108220, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108221 q = 1) (hb : d149255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108221, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108221, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108222 q = 1) (hb : d149256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108222, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108222, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108224 q = 1) (hb : d149259 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108224, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50221 q ha hb
    | true =>
      simp only [d108224, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108225 q = 1) (hb : d149260 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108225, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108225, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108226 q = 1) (hb : d149261 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108226, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108226, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108227 q = 1) (hb : d149262 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108227, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108227, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108232 q = 1) (hb : d149267 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108232, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108232, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108233 q = 1) (hb : d149268 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108233, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108233, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108234 q = 1) (hb : d149269 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108234, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108234, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50224 (p : Pattern) (ha : d108240 p = 1) (hb : d149275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108230 q = 1) (hb : d149265 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108230, d149265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50222 q ha hb
    | true =>
      simp only [d108230, d149265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108231 q = 1) (hb : d149266 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108231, d149266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108231, d149266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108235 q = 1) (hb : d149270 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108235, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50223 q ha hb
    | true =>
      simp only [d108235, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108236 q = 1) (hb : d149271 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108236, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108236, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108237 q = 1) (hb : d149272 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108237, d149272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108237, d149272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108238 q = 1) (hb : d149273 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108238, d149273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108238, d149273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108239 q = 1) (hb : d149274 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108239, d149274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108239, d149274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108240 q = 1) (hb : d149275 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108240, d149275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108240, d149275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50225 (p : Pattern) (ha : d108242 p = 1) (hb : d149277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108224 q = 1) (hb : d149259 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108224, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50221 q ha hb
    | true =>
      simp only [d108224, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108225 q = 1) (hb : d149260 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108225, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108225, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108226 q = 1) (hb : d149261 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108226, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108226, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108232 q = 1) (hb : d149267 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108232, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108232, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108241 q = 1) (hb : d149276 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108241, d149276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108241, d149276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108242 q = 1) (hb : d149277 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108242, d149277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108242, d149277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50226 (p : Pattern) (ha : d108248 p = 1) (hb : d149283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108235 q = 1) (hb : d149270 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108235, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50223 q ha hb
    | true =>
      simp only [d108235, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108236 q = 1) (hb : d149271 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108236, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108236, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108243 q = 1) (hb : d149278 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108243, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50225 q ha hb
    | true =>
      simp only [d108243, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108244 q = 1) (hb : d149279 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108244, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108244, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108245 q = 1) (hb : d149280 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108245, d149280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108245, d149280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108246 q = 1) (hb : d149281 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108246, d149281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108246, d149281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108247 q = 1) (hb : d149282 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108247, d149282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108247, d149282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108248 q = 1) (hb : d149283 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108248, d149283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108248, d149283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50227 (p : Pattern) (ha : d74315 p = 1) (hb : d149258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22043 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22043, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22043, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
  have h2 (q : Pattern) (ha : d21742 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
    | true =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22044 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22044, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22044, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21743 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22045 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22045, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22045, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22046 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22046, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22046, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22064 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22064, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22064, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33425 q ha hb
  have h8 (q : Pattern) (ha : d21755 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33425 q ha hb
    | true =>
      simp only [d21755, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22065 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22065, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22065, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21756 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21756, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22066 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22066, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22066, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22067 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22067, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22067, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22068 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22068, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22068, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74314 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74315 q = 1) (hb : d149258 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74315, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d74315, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro50228 (p : Pattern) (ha : d108261 p = 1) (hb : d149269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108220 q = 1) (hb : d149254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108220, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50220 q ha hb
    | true =>
      simp only [d108220, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108221 q = 1) (hb : d149255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108221, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108221, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108222 q = 1) (hb : d149256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108222, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108222, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108224 q = 1) (hb : d149259 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108224, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50221 q ha hb
    | true =>
      simp only [d108224, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108225 q = 1) (hb : d149260 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108225, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108225, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108226 q = 1) (hb : d149261 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108226, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108226, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108227 q = 1) (hb : d149262 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108227, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108227, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108256 q = 1) (hb : d149259 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108256, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50227 q ha hb
    | true =>
      simp only [d108256, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108257 q = 1) (hb : d149260 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108257, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108257, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108258 q = 1) (hb : d149261 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108258, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108258, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108259 q = 1) (hb : d149267 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108259, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108259, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108260 q = 1) (hb : d149268 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108260, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108260, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108261 q = 1) (hb : d149269 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108261, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108261, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro50229 (p : Pattern) (ha : d108267 p = 1) (hb : d149289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108262 q = 1) (hb : d149270 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108262, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50228 q ha hb
    | true =>
      simp only [d108262, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108263 q = 1) (hb : d149271 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108263, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108263, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108264 q = 1) (hb : d149286 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108264, d149286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108264, d149286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108265 q = 1) (hb : d149287 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108265, d149287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108265, d149287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108266 q = 1) (hb : d149288 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108266, d149288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108266, d149288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108267 q = 1) (hb : d149289 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108267, d149289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108267, d149289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50230 (p : Pattern) (ha : d108273 p = 1) (hb : d149295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108249 q = 1) (hb : d149284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108249, d149284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50224 q ha hb
    | true =>
      simp only [d108249, d149284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50226 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108254 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108255 q = 1) (hb : d149285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108255, d149285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108255, d149285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108268 q = 1) (hb : d149290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108268, d149290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50229 q ha hb
    | true =>
      simp only [d108268, d149290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108269 q = 1) (hb : d149291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108269, d149291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108269, d149291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108270 q = 1) (hb : d149292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108270, d149292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108270, d149292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108271 q = 1) (hb : d149293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108271, d149293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108271, d149293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108272 q = 1) (hb : d149294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108272, d149294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108272, d149294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108273 q = 1) (hb : d149295 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108273, d149295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108273, d149295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro50231 (p : Pattern) (ha : d108253 p = 1) (hb : d149300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108243 q = 1) (hb : d149278 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108243, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50225 q ha hb
    | true =>
      simp only [d108243, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108244 q = 1) (hb : d149279 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108244, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108244, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108250 q = 1) (hb : d149297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108250, d149297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108250, d149297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108251 q = 1) (hb : d149298 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108251, d149298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108251, d149298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108252 q = 1) (hb : d149299 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108252, d149299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108252, d149299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108253 q = 1) (hb : d149300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108253, d149300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108253, d149300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50232 (p : Pattern) (ha : d108280 p = 1) (hb : d149306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108275 q = 1) (hb : d149301 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108275, d149301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50231 q ha hb
    | true =>
      simp only [d108275, d149301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108276 q = 1) (hb : d149302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108276, d149302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108276, d149302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108277 q = 1) (hb : d149303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108277, d149303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108277, d149303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108278 q = 1) (hb : d149304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108278, d149304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108278, d149304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108279 q = 1) (hb : d149305 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108279, d149305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108279, d149305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108280 q = 1) (hb : d149306 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108280, d149306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108280, d149306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50233 (p : Pattern) (ha : d108286 p = 1) (hb : d149312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108107 q = 1) (hb : d149146 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108107, d149146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108107, d149146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50193 q ha hb
  have h2 (q : Pattern) (ha : d108108 q = 1) (hb : d149147 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108108, d149147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108108, d149147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108117 q = 1) (hb : d149156 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108117, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50193 q ha hb
    | true =>
      simp only [d108117, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50196 q ha hb
  have h4 (q : Pattern) (ha : d108118 q = 1) (hb : d149157 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108118, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108118, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108119 q = 1) (hb : d149158 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108119, d149158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108119, d149158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108190 q = 1) (hb : d149222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108190, d149222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50207 q ha hb
    | true =>
      simp only [d108190, d149222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50214 q ha hb
  have h7 (q : Pattern) (ha : d108203 q = 1) (hb : d149235 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108203, d149235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50215 q ha hb
    | true =>
      simp only [d108203, d149235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50216 q ha hb
  have h8 (q : Pattern) (ha : d108204 q = 1) (hb : d149236 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108204, d149236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108204, d149236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108205 q = 1) (hb : d149237 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108205, d149237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108205, d149237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d108206 q = 1) (hb : d149238 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108206, d149238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108206, d149238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108210 q = 1) (hb : d149242 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108210, d149242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108210, d149242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50217 q ha hb
  have h12 (q : Pattern) (ha : d108212 q = 1) (hb : d149244 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108212, d149244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108212, d149244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50218 q ha hb
  have h13 (q : Pattern) (ha : d108213 q = 1) (hb : d149245 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108213, d149245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108213, d149245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108214 q = 1) (hb : d149246 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108214, d149246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108214, d149246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d108215 q = 1) (hb : d149247 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108215, d149247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108215, d149247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d108216 q = 1) (hb : d149248 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108216, d149248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108216, d149248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108274 q = 1) (hb : d149296 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108274, d149296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108274, d149296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50230 q ha hb
  have h18 (q : Pattern) (ha : d108281 q = 1) (hb : d149307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108281, d149307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108281, d149307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50232 q ha hb
  have h19 (q : Pattern) (ha : d108282 q = 1) (hb : d149308 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108282, d149308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108282, d149308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108283 q = 1) (hb : d149309 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108283, d149309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108283, d149309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108284 q = 1) (hb : d149310 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108284, d149310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108284, d149310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108285 q = 1) (hb : d149311 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108285, d149311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108285, d149311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108286 q = 1) (hb : d149312 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108286, d149312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108286, d149312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro50234 (p : Pattern) (ha : d108292 p = 1) (hb : d149318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108287 q = 1) (hb : d149313 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108287, d149313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108287, d149313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50233 q ha hb
  have h2 (q : Pattern) (ha : d108288 q = 1) (hb : d149314 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108288, d149314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108288, d149314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108289 q = 1) (hb : d149315 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108289, d149315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108289, d149315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108290 q = 1) (hb : d149316 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108290, d149316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108290, d149316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108291 q = 1) (hb : d149317 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108291, d149317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108291, d149317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108292 q = 1) (hb : d149318 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108292, d149318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108292, d149318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50235 (p : Pattern) (ha : d53028 p = 1) (hb : d149322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10036 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
    | true =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10038 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16859 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16860 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16860, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22220 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
    | true =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22221 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22222 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22222, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22222, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22223 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22223, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22223, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22224 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22224, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22224, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53028 q = 1) (hb : d149322 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53028, d149322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d53028, d149322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50236 (p : Pattern) (ha : d53030 p = 1) (hb : d149326 p = 1) : d0 p = 1 := by
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
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53030 q = 1) (hb : d149326 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53030, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d53030, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro50237 (p : Pattern) (ha : d108305 p = 1) (hb : d149333 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d108303 q = 1) (hb : d149331 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108303, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108303, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108304 q = 1) (hb : d149332 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108304, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108304, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108305 q = 1) (hb : d149333 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108305, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108305, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro50238 (p : Pattern) (ha : d108309 p = 1) (hb : d149337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108299 q = 1) (hb : d149327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108299, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50236 q ha hb
    | true =>
      simp only [d108299, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108300 q = 1) (hb : d149328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108300, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108300, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108301 q = 1) (hb : d149329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108301, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108301, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108303 q = 1) (hb : d149331 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108303, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108303, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108308 q = 1) (hb : d149336 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108308, d149336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108308, d149336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108309 q = 1) (hb : d149337 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108309, d149337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108309, d149337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50239 (p : Pattern) (ha : d108315 p = 1) (hb : d149343 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d108314 q = 1) (hb : d149342 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108314, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108314, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108315 q = 1) (hb : d149343 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108315, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108315, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50240 (p : Pattern) (ha : d108319 p = 1) (hb : d149347 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d108318 q = 1) (hb : d149346 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108318, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108318, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108319 q = 1) (hb : d149347 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108319, d149347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108319, d149347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50241 (p : Pattern) (ha : d108325 p = 1) (hb : d149353 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d108325 q = 1) (hb : d149353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108325, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108325, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50242 (p : Pattern) (ha : d108328 p = 1) (hb : d149356 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d108314 q = 1) (hb : d149342 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108314, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108314, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108328 q = 1) (hb : d149356 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108328, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108328, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro50243 (p : Pattern) (ha : d108329 p = 1) (hb : d149357 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d108318 q = 1) (hb : d149346 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108318, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108318, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108329 q = 1) (hb : d149357 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108329, d149357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108329, d149357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro50244 (p : Pattern) (ha : d108335 p = 1) (hb : d149363 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d108330 q = 1) (hb : d149358 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108330, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50242 q ha hb
    | true =>
      simp only [d108330, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50243 q ha hb
  have h7 (q : Pattern) (ha : d108331 q = 1) (hb : d149359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108331, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108331, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108332 q = 1) (hb : d149360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108332, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108332, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108333 q = 1) (hb : d149361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108333, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108333, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108334 q = 1) (hb : d149362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108334, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108334, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108335 q = 1) (hb : d149363 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108335, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108335, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro50245 (p : Pattern) (ha : d108340 p = 1) (hb : d149368 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d108340 q = 1) (hb : d149368 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108340, d149368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108340, d149368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50246 (p : Pattern) (ha : d108342 p = 1) (hb : d149370 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d108342 q = 1) (hb : d149370 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108342, d149370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108342, d149370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50247 (p : Pattern) (ha : d108349 p = 1) (hb : d149377 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d108349 q = 1) (hb : d149377 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108349, d149377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108349, d149377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro50248 (p : Pattern) (ha : d108352 p = 1) (hb : d149380 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d108352 q = 1) (hb : d149380 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108352, d149380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108352, d149380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro50249 (p : Pattern) (ha : d53111 p = 1) (hb : d149384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22313 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22313, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46225 q ha hb
    | true =>
      simp only [d22313, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22314 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22314, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22314, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22315 q = 1) (hb : d53108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22315, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22315, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22316 q = 1) (hb : d53109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22316, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22316, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10036 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
    | true =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10038 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16859 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16860 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16860, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22317 q = 1) (hb : d53110 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22317, d53110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22317, d53110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53111 q = 1) (hb : d149384 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53111, d149384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d53111, d149384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
end NetHack.Soko22Hazard87
