import NetHack.Soko22Hazard87.AndIntroBlocks0391
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro98000 (p : Pattern) (ha : d263456 p = 1) (hb : d323604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263450 q = 1) (hb : d323579 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263450, d323579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263450, d323579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97976 q ha hb
  have h2 (q : Pattern) (ha : d263313 q = 1) (hb : d323372 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263313, d323372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97976 q ha hb
    | true =>
      simp only [d263313, d323372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263451 q = 1) (hb : d323580 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263451, d323580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263451, d323580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263314 q = 1) (hb : d323373 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263314, d323373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263314, d323373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263452 q = 1) (hb : d323581 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263452, d323581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263452, d323581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263453 q = 1) (hb : d323582 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263453, d323582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263453, d323582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263441 q = 1) (hb : d323594 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263441, d323594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263441, d323594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97955 q ha hb
  have h8 (q : Pattern) (ha : d263199 q = 1) (hb : d323381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263199, d323381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97955 q ha hb
    | true =>
      simp only [d263199, d323381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263442 q = 1) (hb : d323595 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263442, d323595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263442, d323595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263200 q = 1) (hb : d323382 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263200, d323382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263200, d323382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263443 q = 1) (hb : d323596 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263443, d323596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263443, d323596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263444 q = 1) (hb : d323597 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263444, d323597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263444, d323597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263454 q = 1) (hb : d323598 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263454, d323598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263454, d323598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263455 q = 1) (hb : d323603 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263455, d323603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263455, d323603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263456 q = 1) (hb : d323604 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263456, d323604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263456, d323604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98001 (p : Pattern) (ha : d263470 p = 1) (hb : d323618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263461 q = 1) (hb : d323609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263461, d323609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263461, d323609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97957 q ha hb
  have h2 (q : Pattern) (ha : d263212 q = 1) (hb : d323394 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263212, d323394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97957 q ha hb
    | true =>
      simp only [d263212, d323394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263462 q = 1) (hb : d323610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263462, d323610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263462, d323610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263213 q = 1) (hb : d323395 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263213, d323395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263213, d323395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263463 q = 1) (hb : d323611 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263463, d323611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263463, d323611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263464 q = 1) (hb : d323612 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263464, d323612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263464, d323612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263465 q = 1) (hb : d323613 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263465, d323613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263465, d323613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97958 q ha hb
  have h8 (q : Pattern) (ha : d263217 q = 1) (hb : d323399 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263217, d323399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97958 q ha hb
    | true =>
      simp only [d263217, d323399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263466 q = 1) (hb : d323614 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263466, d323614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263466, d323614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263218 q = 1) (hb : d323400 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263218, d323400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263218, d323400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263467 q = 1) (hb : d323615 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263467, d323615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263467, d323615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263468 q = 1) (hb : d323616 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263468, d323616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263468, d323616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263469 q = 1) (hb : d323617 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263469, d323617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263469, d323617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263441 q = 1) (hb : d323594 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263441, d323594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263441, d323594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97955 q ha hb
  have h15 (q : Pattern) (ha : d263199 q = 1) (hb : d323381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263199, d323381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97955 q ha hb
    | true =>
      simp only [d263199, d323381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d263442 q = 1) (hb : d323595 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263442, d323595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263442, d323595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263200 q = 1) (hb : d323382 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263200, d323382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263200, d323382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d263443 q = 1) (hb : d323596 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263443, d323596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263443, d323596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d263444 q = 1) (hb : d323597 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263444, d323597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d263444, d323597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d263455 q = 1) (hb : d323603 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263455, d323603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263455, d323603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d263470 q = 1) (hb : d323618 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263470, d323618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263470, d323618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro98002 (p : Pattern) (ha : d263475 p = 1) (hb : d323623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263465 q = 1) (hb : d323613 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263465, d323613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263465, d323613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97958 q ha hb
  have h2 (q : Pattern) (ha : d263217 q = 1) (hb : d323399 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263217, d323399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97958 q ha hb
    | true =>
      simp only [d263217, d323399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263466 q = 1) (hb : d323614 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263466, d323614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263466, d323614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263218 q = 1) (hb : d323400 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263218, d323400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263218, d323400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263467 q = 1) (hb : d323615 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263467, d323615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263467, d323615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263468 q = 1) (hb : d323616 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263468, d323616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263468, d323616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263474 q = 1) (hb : d323622 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263474, d323622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263474, d323622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d123453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d263475 q = 1) (hb : d323623 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263475, d323623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263475, d323623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro98003 (p : Pattern) (ha : d263481 p = 1) (hb : d323629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263447 q = 1) (hb : d323600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263447, d323600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97998 q ha hb
    | true =>
      simp only [d263447, d323600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97999 q ha hb
  have h2 (q : Pattern) (ha : d263448 q = 1) (hb : d323601 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263448, d323601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263448, d323601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263449 q = 1) (hb : d323602 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263449, d323602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263449, d323602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263457 q = 1) (hb : d323605 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263457, d323605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97999 q ha hb
    | true =>
      simp only [d263457, d323605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98000 q ha hb
  have h5 (q : Pattern) (ha : d263458 q = 1) (hb : d323606 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263458, d323606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263458, d323606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263459 q = 1) (hb : d323607 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263459, d323607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263459, d323607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263460 q = 1) (hb : d323608 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263460, d323608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263460, d323608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263471 q = 1) (hb : d323619 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263471, d323619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97999 q ha hb
    | true =>
      simp only [d263471, d323619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98001 q ha hb
  have h9 (q : Pattern) (ha : d263472 q = 1) (hb : d323620 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263472, d323620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263472, d323620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263473 q = 1) (hb : d323621 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263473, d323621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263473, d323621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263476 q = 1) (hb : d323624 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263476, d323624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98001 q ha hb
    | true =>
      simp only [d263476, d323624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98002 q ha hb
  have h12 (q : Pattern) (ha : d263477 q = 1) (hb : d323625 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263477, d323625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263477, d323625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263478 q = 1) (hb : d323626 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263478, d323626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263478, d323626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263479 q = 1) (hb : d323627 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263479, d323627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263479, d323627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d263480 q = 1) (hb : d323628 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263480, d323628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263480, d323628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d263481 q = 1) (hb : d323629 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263481, d323629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263481, d323629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro98004 (p : Pattern) (ha : d263486 p = 1) (hb : d323634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263471 q = 1) (hb : d323619 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263471, d323619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97999 q ha hb
    | true =>
      simp only [d263471, d323619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98001 q ha hb
  have h2 (q : Pattern) (ha : d263472 q = 1) (hb : d323620 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263472, d323620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263472, d323620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263473 q = 1) (hb : d323621 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263473, d323621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263473, d323621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263476 q = 1) (hb : d323624 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263476, d323624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98001 q ha hb
    | true =>
      simp only [d263476, d323624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98002 q ha hb
  have h5 (q : Pattern) (ha : d263477 q = 1) (hb : d323625 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263477, d323625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263477, d323625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263478 q = 1) (hb : d323626 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263478, d323626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263478, d323626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263479 q = 1) (hb : d323627 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263479, d323627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263479, d323627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263484 q = 1) (hb : d323632 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263484, d323632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263484, d323632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263485 q = 1) (hb : d323633 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263485, d323633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263485, d323633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263486 q = 1) (hb : d323634 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263486, d323634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263486, d323634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro98005 (p : Pattern) (ha : d263492 p = 1) (hb : d323640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263482 q = 1) (hb : d323630 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263482, d323630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98003 q ha hb
    | true =>
      simp only [d263482, d323630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263483 q = 1) (hb : d323631 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263483, d323631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263483, d323631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263487 q = 1) (hb : d323635 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263487, d323635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98004 q ha hb
    | true =>
      simp only [d263487, d323635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263488 q = 1) (hb : d323636 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263488, d323636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263488, d323636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263489 q = 1) (hb : d323637 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263489, d323637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263489, d323637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263490 q = 1) (hb : d323638 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263490, d323638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263490, d323638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263491 q = 1) (hb : d323639 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263491, d323639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263491, d323639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263492 q = 1) (hb : d323640 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263492, d323640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263492, d323640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98006 (p : Pattern) (ha : d263494 p = 1) (hb : d323642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263476 q = 1) (hb : d323624 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263476, d323624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98001 q ha hb
    | true =>
      simp only [d263476, d323624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98002 q ha hb
  have h2 (q : Pattern) (ha : d263477 q = 1) (hb : d323625 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263477, d323625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263477, d323625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263478 q = 1) (hb : d323626 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263478, d323626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263478, d323626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263484 q = 1) (hb : d323632 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263484, d323632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263484, d323632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263493 q = 1) (hb : d323641 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263493, d323641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263493, d323641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263494 q = 1) (hb : d323642 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263494, d323642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263494, d323642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98007 (p : Pattern) (ha : d263500 p = 1) (hb : d323648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263487 q = 1) (hb : d323635 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263487, d323635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98004 q ha hb
    | true =>
      simp only [d263487, d323635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263488 q = 1) (hb : d323636 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263488, d323636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263488, d323636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263495 q = 1) (hb : d323643 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263495, d323643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98006 q ha hb
    | true =>
      simp only [d263495, d323643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263496 q = 1) (hb : d323644 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263496, d323644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263496, d323644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263497 q = 1) (hb : d323645 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263497, d323645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263497, d323645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263498 q = 1) (hb : d323646 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263498, d323646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263498, d323646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263499 q = 1) (hb : d323647 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263499, d323647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263499, d323647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263500 q = 1) (hb : d323648 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263500, d323648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263500, d323648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98008 (p : Pattern) (ha : d263513 p = 1) (hb : d323656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263461 q = 1) (hb : d323609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263461, d323609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263461, d323609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97957 q ha hb
  have h2 (q : Pattern) (ha : d263212 q = 1) (hb : d323394 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263212, d323394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97957 q ha hb
    | true =>
      simp only [d263212, d323394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263462 q = 1) (hb : d323610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263462, d323610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263462, d323610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263213 q = 1) (hb : d323395 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263213, d323395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263213, d323395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263463 q = 1) (hb : d323611 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263463, d323611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263463, d323611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263464 q = 1) (hb : d323612 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263464, d323612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263464, d323612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263465 q = 1) (hb : d323613 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263465, d323613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263465, d323613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97958 q ha hb
  have h8 (q : Pattern) (ha : d263217 q = 1) (hb : d323399 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263217, d323399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97958 q ha hb
    | true =>
      simp only [d263217, d323399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263466 q = 1) (hb : d323614 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263466, d323614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263466, d323614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263218 q = 1) (hb : d323400 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263218, d323400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263218, d323400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263467 q = 1) (hb : d323615 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263467, d323615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263467, d323615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263468 q = 1) (hb : d323616 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263468, d323616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263468, d323616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263469 q = 1) (hb : d323617 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263469, d323617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263469, d323617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263508 q = 1) (hb : d323651 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263508, d323651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263508, d323651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97980 q ha hb
  have h15 (q : Pattern) (ha : d263334 q = 1) (hb : d323495 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263334, d323495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97980 q ha hb
    | true =>
      simp only [d263334, d323495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d263509 q = 1) (hb : d323652 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263509, d323652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263509, d323652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263335 q = 1) (hb : d323496 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263335, d323496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263335, d323496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d263510 q = 1) (hb : d323653 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263510, d323653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263510, d323653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d263511 q = 1) (hb : d323654 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263511, d323654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d263511, d323654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d263512 q = 1) (hb : d323655 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263512, d323655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263512, d323655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d263513 q = 1) (hb : d323656 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263513, d323656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263513, d323656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro98009 (p : Pattern) (ha : d263519 p = 1) (hb : d323662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263514 q = 1) (hb : d323657 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263514, d323657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263514, d323657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97982 q ha hb
  have h2 (q : Pattern) (ha : d263341 q = 1) (hb : d323502 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263341, d323502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97982 q ha hb
    | true =>
      simp only [d263341, d323502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263515 q = 1) (hb : d323658 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263515, d323658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263515, d323658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263342 q = 1) (hb : d323503 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263342, d323503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263342, d323503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263516 q = 1) (hb : d323659 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263516, d323659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263516, d323659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263517 q = 1) (hb : d323660 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263517, d323660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263517, d323660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263518 q = 1) (hb : d323661 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263518, d323661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263518, d323661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263519 q = 1) (hb : d323662 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263519, d323662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263519, d323662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98010 (p : Pattern) (ha : d263525 p = 1) (hb : d323668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263471 q = 1) (hb : d323619 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263471, d323619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97999 q ha hb
    | true =>
      simp only [d263471, d323619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98001 q ha hb
  have h2 (q : Pattern) (ha : d263472 q = 1) (hb : d323620 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263472, d323620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263472, d323620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263473 q = 1) (hb : d323621 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263473, d323621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263473, d323621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263476 q = 1) (hb : d323624 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263476, d323624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98001 q ha hb
    | true =>
      simp only [d263476, d323624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98002 q ha hb
  have h5 (q : Pattern) (ha : d263477 q = 1) (hb : d323625 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263477, d323625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263477, d323625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263478 q = 1) (hb : d323626 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263478, d323626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263478, d323626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263479 q = 1) (hb : d323627 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263479, d323627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263479, d323627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263520 q = 1) (hb : d323663 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263520, d323663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98008 q ha hb
    | true =>
      simp only [d263520, d323663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98009 q ha hb
  have h9 (q : Pattern) (ha : d263521 q = 1) (hb : d323664 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263521, d323664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263521, d323664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263522 q = 1) (hb : d323665 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263522, d323665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263522, d323665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263523 q = 1) (hb : d323666 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263523, d323666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263523, d323666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263524 q = 1) (hb : d323667 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263524, d323667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263524, d323667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263525 q = 1) (hb : d323668 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263525, d323668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263525, d323668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro98011 (p : Pattern) (ha : d263531 p = 1) (hb : d323674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263526 q = 1) (hb : d323669 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263526, d323669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98010 q ha hb
    | true =>
      simp only [d263526, d323669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263527 q = 1) (hb : d323670 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263527, d323670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263527, d323670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263528 q = 1) (hb : d323671 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263528, d323671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263528, d323671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263529 q = 1) (hb : d323672 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263529, d323672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263529, d323672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263530 q = 1) (hb : d323673 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263530, d323673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263530, d323673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263531 q = 1) (hb : d323674 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263531, d323674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263531, d323674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98012 (p : Pattern) (ha : d263537 p = 1) (hb : d323680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263501 q = 1) (hb : d323649 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263501, d323649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98005 q ha hb
    | true =>
      simp only [d263501, d323649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98007 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263506 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263507 q = 1) (hb : d323650 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263507, d323650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263507, d323650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d263532 q = 1) (hb : d323675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263532, d323675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98011 q ha hb
    | true =>
      simp only [d263532, d323675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263533 q = 1) (hb : d323676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263533, d323676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263533, d323676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263534 q = 1) (hb : d323677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263534, d323677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263534, d323677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263535 q = 1) (hb : d323678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263535, d323678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263535, d323678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263536 q = 1) (hb : d323679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263536, d323679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263536, d323679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263537 q = 1) (hb : d323680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263537, d323680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263537, d323680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro98013 (p : Pattern) (ha : d263505 p = 1) (hb : d323685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263495 q = 1) (hb : d323643 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263495, d323643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98006 q ha hb
    | true =>
      simp only [d263495, d323643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263496 q = 1) (hb : d323644 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263496, d323644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263496, d323644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263502 q = 1) (hb : d323682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263502, d323682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263502, d323682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263503 q = 1) (hb : d323683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263503, d323683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263503, d323683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263504 q = 1) (hb : d323684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263504, d323684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263504, d323684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263505 q = 1) (hb : d323685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263505, d323685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263505, d323685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98014 (p : Pattern) (ha : d263544 p = 1) (hb : d323691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263539 q = 1) (hb : d323686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263539, d323686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98013 q ha hb
    | true =>
      simp only [d263539, d323686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263540 q = 1) (hb : d323687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263540, d323687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263540, d323687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263541 q = 1) (hb : d323688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263541, d323688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263541, d323688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263542 q = 1) (hb : d323689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263542, d323689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263542, d323689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263543 q = 1) (hb : d323690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263543, d323690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263543, d323690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263544 q = 1) (hb : d323691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263544, d323691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263544, d323691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98015 (p : Pattern) (ha : d263550 p = 1) (hb : d323697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263256 q = 1) (hb : d323438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263256, d323438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263256, d323438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97965 q ha hb
  have h2 (q : Pattern) (ha : d263257 q = 1) (hb : d323439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263257, d323439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263257, d323439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263266 q = 1) (hb : d323448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263266, d323448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97965 q ha hb
    | true =>
      simp only [d263266, d323448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97968 q ha hb
  have h4 (q : Pattern) (ha : d263267 q = 1) (hb : d323449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263267, d323449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263267, d323449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263268 q = 1) (hb : d323450 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263268, d323450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263268, d323450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263386 q = 1) (hb : d323547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263386, d323547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97986 q ha hb
    | true =>
      simp only [d263386, d323547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97993 q ha hb
  have h7 (q : Pattern) (ha : d263399 q = 1) (hb : d323560 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263399, d323560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97994 q ha hb
    | true =>
      simp only [d263399, d323560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97995 q ha hb
  have h8 (q : Pattern) (ha : d263400 q = 1) (hb : d323561 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263400, d323561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263400, d323561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263401 q = 1) (hb : d323562 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263401, d323562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263401, d323562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d263402 q = 1) (hb : d323563 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263402, d323563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263402, d323563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263406 q = 1) (hb : d323567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263406, d323567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263406, d323567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97996 q ha hb
  have h12 (q : Pattern) (ha : d263408 q = 1) (hb : d323569 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263408, d323569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263408, d323569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97997 q ha hb
  have h13 (q : Pattern) (ha : d263409 q = 1) (hb : d323570 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263409, d323570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263409, d323570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263410 q = 1) (hb : d323571 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263410, d323571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263410, d323571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263411 q = 1) (hb : d323572 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263411, d323572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263411, d323572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d263412 q = 1) (hb : d323573 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263412, d323573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263412, d323573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263538 q = 1) (hb : d323681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263538, d323681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263538, d323681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98012 q ha hb
  have h18 (q : Pattern) (ha : d263545 q = 1) (hb : d323692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263545, d323692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263545, d323692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98014 q ha hb
  have h19 (q : Pattern) (ha : d263546 q = 1) (hb : d323693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263546, d323693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263546, d323693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d263547 q = 1) (hb : d323694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263547, d323694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263547, d323694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d263548 q = 1) (hb : d323695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263548, d323695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d263548, d323695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d263549 q = 1) (hb : d323696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263549, d323696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d263549, d323696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d263550 q = 1) (hb : d323697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263550, d323697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263550, d323697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro98016 (p : Pattern) (ha : d263556 p = 1) (hb : d323703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263551 q = 1) (hb : d323698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263551, d323698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263551, d323698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98015 q ha hb
  have h2 (q : Pattern) (ha : d263552 q = 1) (hb : d323699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263552, d323699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263552, d323699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263553 q = 1) (hb : d323700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263553, d323700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263553, d323700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263554 q = 1) (hb : d323701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263554, d323701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263554, d323701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263555 q = 1) (hb : d323702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263555, d323702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263555, d323702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263556 q = 1) (hb : d323703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263556, d323703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263556, d323703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98017 (p : Pattern) (ha : d263580 p = 1) (hb : d323711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263565 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d35376 q = 1) (hb : d263575 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35376, d263575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77418 q ha hb
    | true =>
      simp only [d35376, d263575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35377 q = 1) (hb : d263576 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35377, d263576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35377, d263576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d263577 q = 1) (hb : d323708 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d263577, d323708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263577, d323708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263578 q = 1) (hb : d323709 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d263578, d323709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263578, d323709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d263579 q = 1) (hb : d323710 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d263579, d323710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263579, d323710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d263580 q = 1) (hb : d323711 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263580, d323711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263580, d323711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98018 (p : Pattern) (ha : d263586 p = 1) (hb : d323711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d35376 q = 1) (hb : d263575 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35376, d263575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77418 q ha hb
    | true =>
      simp only [d35376, d263575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d35377 q = 1) (hb : d263576 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35377, d263576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35377, d263576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d263577 q = 1) (hb : d323708 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d263577, d323708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263577, d323708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d263578 q = 1) (hb : d323709 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d263578, d323709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263578, d323709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263579 q = 1) (hb : d323710 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d263579, d323710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263579, d323710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263586 q = 1) (hb : d323711 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263586, d323711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263586, d323711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro98019 (p : Pattern) (ha : d263597 p = 1) (hb : d323717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d35376 q = 1) (hb : d263575 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35376, d263575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77418 q ha hb
    | true =>
      simp only [d35376, d263575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35377 q = 1) (hb : d263576 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35377, d263576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35377, d263576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d263594 q = 1) (hb : d323708 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d263594, d323708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263594, d323708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d263595 q = 1) (hb : d323709 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d263595, d323709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263595, d323709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d263596 q = 1) (hb : d323710 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d263596, d323710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263596, d323710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d2058 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h8 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h9 (q : Pattern) (ha : d2059 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2060 q = 1) (hb : d53339 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10405 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
    | true =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10406 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
    | true =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d10407 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10408 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d32713 q = 1) (hb : d243370 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32713, d243370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32713, d243370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d32714 q = 1) (hb : d243371 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32714, d243371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d32714, d243371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d263597 q = 1) (hb : d323717 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263597, d323717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263597, d323717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  exact h19 p ha hb
theorem andIntro98020 (p : Pattern) (ha : d263603 p = 1) (hb : d323723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263570 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263581 q = 1) (hb : d323712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263581, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98017 q ha hb
    | true =>
      simp only [d263581, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d263582 q = 1) (hb : d323713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263582, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263582, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d263583 q = 1) (hb : d323714 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263583, d323714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263583, d323714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263584 q = 1) (hb : d323715 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263584, d323715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263584, d323715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d263585 q = 1) (hb : d323716 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263585, d323716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263585, d323716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263587 q = 1) (hb : d323712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98018 q ha hb
    | true =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d263588 q = 1) (hb : d323713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d263589 q = 1) (hb : d323714 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263589, d323714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263589, d323714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263590 q = 1) (hb : d323715 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263590, d323715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263590, d323715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d263598 q = 1) (hb : d323718 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98019 q ha hb
    | true =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d263599 q = 1) (hb : d323719 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d263600 q = 1) (hb : d323720 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263600, d323720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263600, d323720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263601 q = 1) (hb : d323721 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263601, d323721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263601, d323721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d263602 q = 1) (hb : d323722 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263602, d323722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263602, d323722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d263603 q = 1) (hb : d323723 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263603, d323723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263603, d323723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro98021 (p : Pattern) (ha : d263610 p = 1) (hb : d323727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263565 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263593 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d35427 q = 1) (hb : d263605 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35427, d263605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77423 q ha hb
    | true =>
      simp only [d35427, d263605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d35428 q = 1) (hb : d263606 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35428, d263606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35428, d263606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263607 q = 1) (hb : d323724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d263607, d323724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263607, d323724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d30103 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30103, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263608 q = 1) (hb : d323725 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d263608, d323725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263608, d323725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d263609 q = 1) (hb : d323726 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d263609, d323726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263609, d323726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d263610 q = 1) (hb : d323727 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263610, d323727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263610, d323727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro98022 (p : Pattern) (ha : d263615 p = 1) (hb : d323732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35427 q = 1) (hb : d263605 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35427, d263605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77423 q ha hb
    | true =>
      simp only [d35427, d263605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d35428 q = 1) (hb : d263606 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35428, d263606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35428, d263606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263607 q = 1) (hb : d323724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d263607, d323724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263607, d323724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d30103 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30103, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263608 q = 1) (hb : d323725 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d263608, d323725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263608, d323725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263609 q = 1) (hb : d323726 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d263609, d323726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263609, d323726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h11 (q : Pattern) (ha : d2058 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h12 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h13 (q : Pattern) (ha : d2059 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2060 q = 1) (hb : d53339 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d10405 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
    | true =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d10406 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
    | true =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d10407 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10408 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d32713 q = 1) (hb : d243370 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32713, d243370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32713, d243370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d32714 q = 1) (hb : d243371 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32714, d243371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32714, d243371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h21 (q : Pattern) (ha : d263615 q = 1) (hb : d323732 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263615, d323732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263615, d323732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro98023 (p : Pattern) (ha : d263622 p = 1) (hb : d323739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263611 q = 1) (hb : d323728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263611, d323728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98021 q ha hb
    | true =>
      simp only [d263611, d323728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263612 q = 1) (hb : d323729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263612, d323729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263612, d323729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263613 q = 1) (hb : d323730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263613, d323730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263613, d323730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263614 q = 1) (hb : d323731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263614, d323731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263614, d323731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263616 q = 1) (hb : d323733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98022 q ha hb
    | true =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263617 q = 1) (hb : d323734 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263618 q = 1) (hb : d323735 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263618, d323735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263618, d323735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263619 q = 1) (hb : d323736 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263619, d323736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263619, d323736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263620 q = 1) (hb : d323737 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263620, d323737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263620, d323737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263598 q = 1) (hb : d323718 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98019 q ha hb
    | true =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263599 q = 1) (hb : d323719 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263600 q = 1) (hb : d323720 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263600, d323720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263600, d323720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263601 q = 1) (hb : d323721 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263601, d323721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263601, d323721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d263621 q = 1) (hb : d323738 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263621, d323738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263621, d323738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263622 q = 1) (hb : d323739 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263622, d323739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263622, d323739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98024 (p : Pattern) (ha : d263631 p = 1) (hb : d323732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35427 q = 1) (hb : d263626 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35427, d263626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77418 q ha hb
    | true =>
      simp only [d35427, d263626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d35428 q = 1) (hb : d263627 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35428, d263627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35428, d263627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263628 q = 1) (hb : d323724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d263628, d323724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263628, d323724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d30103 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30103, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263629 q = 1) (hb : d323725 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d263629, d323725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263629, d323725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263630 q = 1) (hb : d323726 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d263630, d323726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263630, d323726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h11 (q : Pattern) (ha : d2058 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h12 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h13 (q : Pattern) (ha : d2059 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2060 q = 1) (hb : d53339 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d10405 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
    | true =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d10406 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
    | true =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d10407 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10408 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d32713 q = 1) (hb : d243370 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32713, d243370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32713, d243370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d32714 q = 1) (hb : d243371 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32714, d243371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32714, d243371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h21 (q : Pattern) (ha : d263631 q = 1) (hb : d323732 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263631, d323732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263631, d323732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro98025 (p : Pattern) (ha : d263637 p = 1) (hb : d323744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263632 q = 1) (hb : d323733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263632, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98024 q ha hb
    | true =>
      simp only [d263632, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263633 q = 1) (hb : d323734 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263633, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263633, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263634 q = 1) (hb : d323735 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263634, d323735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263634, d323735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263635 q = 1) (hb : d323736 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263635, d323736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263635, d323736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263636 q = 1) (hb : d323743 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263636, d323743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263636, d323743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15555 q = 1) (hb : d123554 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15556 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15557 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d263637 q = 1) (hb : d323744 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263637, d323744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263637, d323744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro98026 (p : Pattern) (ha : d263643 p = 1) (hb : d323744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263616 q = 1) (hb : d323733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98022 q ha hb
    | true =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263617 q = 1) (hb : d323734 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263618 q = 1) (hb : d323735 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263618, d323735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263618, d323735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263619 q = 1) (hb : d323736 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263619, d323736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263619, d323736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263642 q = 1) (hb : d323743 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263642, d323743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263642, d323743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15555 q = 1) (hb : d123554 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15556 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15557 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d263643 q = 1) (hb : d323744 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263643, d323744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263643, d323744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro98027 (p : Pattern) (ha : d263649 p = 1) (hb : d323751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263623 q = 1) (hb : d323740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263623, d323740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98020 q ha hb
    | true =>
      simp only [d263623, d323740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98023 q ha hb
  have h2 (q : Pattern) (ha : d263624 q = 1) (hb : d323741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263624, d323741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263624, d323741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263625 q = 1) (hb : d323742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263625, d323742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263625, d323742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263638 q = 1) (hb : d323745 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263638, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98023 q ha hb
    | true =>
      simp only [d263638, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98025 q ha hb
  have h5 (q : Pattern) (ha : d263639 q = 1) (hb : d323746 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263639, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263639, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263640 q = 1) (hb : d323747 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263640, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263640, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263641 q = 1) (hb : d323748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263641, d323748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263641, d323748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263644 q = 1) (hb : d323745 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263644, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98023 q ha hb
    | true =>
      simp only [d263644, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98026 q ha hb
  have h9 (q : Pattern) (ha : d263645 q = 1) (hb : d323746 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263645, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263645, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263646 q = 1) (hb : d323747 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263646, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263646, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263647 q = 1) (hb : d323749 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263647, d323749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263647, d323749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263648 q = 1) (hb : d323750 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263648, d323750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263648, d323750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263649 q = 1) (hb : d323751 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263649, d323751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263649, d323751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro98028 (p : Pattern) (ha : d263653 p = 1) (hb : d323755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263644 q = 1) (hb : d323745 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263644, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98023 q ha hb
    | true =>
      simp only [d263644, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98026 q ha hb
  have h2 (q : Pattern) (ha : d263645 q = 1) (hb : d323746 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263645, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263645, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263646 q = 1) (hb : d323747 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263646, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263646, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263647 q = 1) (hb : d323749 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263647, d323749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263647, d323749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263652 q = 1) (hb : d323754 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263652, d323754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263652, d323754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263653 q = 1) (hb : d323755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263653, d323755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263653, d323755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98029 (p : Pattern) (ha : d263659 p = 1) (hb : d323761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d323752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98027 q ha hb
    | true =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d323753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d323758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263657 q = 1) (hb : d323759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263657, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263657, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263658 q = 1) (hb : d323760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263658, d323760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263658, d323760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263659 q = 1) (hb : d323761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263659, d323761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263659, d323761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98030 (p : Pattern) (ha : d263663 p = 1) (hb : d323765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d323762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263661 q = 1) (hb : d323763 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263661, d323763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263661, d323763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263662 q = 1) (hb : d323764 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263662, d323764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263662, d323764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263663 q = 1) (hb : d323765 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263663, d323765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263663, d323765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98031 (p : Pattern) (ha : d263669 p = 1) (hb : d323771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263664 q = 1) (hb : d323766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263664, d323766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98029 q ha hb
    | true =>
      simp only [d263664, d323766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98030 q ha hb
  have h2 (q : Pattern) (ha : d263665 q = 1) (hb : d323767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263665, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263665, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263666 q = 1) (hb : d323768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263666, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263666, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263667 q = 1) (hb : d323769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263667, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263667, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263668 q = 1) (hb : d323770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263668, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263668, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263669 q = 1) (hb : d323771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263669, d323771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263669, d323771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98032 (p : Pattern) (ha : d263672 p = 1) (hb : d323774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d323752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98027 q ha hb
    | true =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d323753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d323758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263657 q = 1) (hb : d323759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263657, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263657, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263658 q = 1) (hb : d323760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263658, d323760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263658, d323760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263672 q = 1) (hb : d323774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263672, d323774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263672, d323774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98033 (p : Pattern) (ha : d263673 p = 1) (hb : d323775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d323762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263661 q = 1) (hb : d323763 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263661, d323763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263661, d323763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263662 q = 1) (hb : d323764 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263662, d323764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263662, d323764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263673 q = 1) (hb : d323775 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263673, d323775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263673, d323775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98034 (p : Pattern) (ha : d263679 p = 1) (hb : d323781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263664 q = 1) (hb : d323766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263664, d323766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98029 q ha hb
    | true =>
      simp only [d263664, d323766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98030 q ha hb
  have h2 (q : Pattern) (ha : d263665 q = 1) (hb : d323767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263665, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263665, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263666 q = 1) (hb : d323768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263666, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263666, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263667 q = 1) (hb : d323769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263667, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263667, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263668 q = 1) (hb : d323770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263668, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263668, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263674 q = 1) (hb : d323776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263674, d323776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98032 q ha hb
    | true =>
      simp only [d263674, d323776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98033 q ha hb
  have h7 (q : Pattern) (ha : d263675 q = 1) (hb : d323777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263675, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263675, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263676 q = 1) (hb : d323778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263676, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263676, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263677 q = 1) (hb : d323779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263677, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263677, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263678 q = 1) (hb : d323780 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263678, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263678, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263679 q = 1) (hb : d323781 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263679, d323781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263679, d323781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98035 (p : Pattern) (ha : d263684 p = 1) (hb : d323786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d323752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98027 q ha hb
    | true =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d323753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d323758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263657 q = 1) (hb : d323759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263657, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263657, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263683 q = 1) (hb : d323785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263683, d323785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263683, d323785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263684 q = 1) (hb : d323786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263684, d323786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263684, d323786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98036 (p : Pattern) (ha : d263686 p = 1) (hb : d323788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d323762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263661 q = 1) (hb : d323763 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263661, d323763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263661, d323763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263685 q = 1) (hb : d323787 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263685, d323787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263685, d323787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263686 q = 1) (hb : d323788 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263686, d323788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263686, d323788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98037 (p : Pattern) (ha : d263693 p = 1) (hb : d323795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d323752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98027 q ha hb
    | true =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d323753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d323758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263691 q = 1) (hb : d323793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263691, d323793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263691, d323793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263692 q = 1) (hb : d323794 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263692, d323794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263692, d323794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263693 q = 1) (hb : d323795 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263693, d323795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263693, d323795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98038 (p : Pattern) (ha : d263696 p = 1) (hb : d323798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d323762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263694 q = 1) (hb : d323796 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263694, d323796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263694, d323796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263695 q = 1) (hb : d323797 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263695, d323797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263695, d323797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263696 q = 1) (hb : d323798 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263696, d323798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263696, d323798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98039 (p : Pattern) (ha : d263701 p = 1) (hb : d323802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263587 q = 1) (hb : d323712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98018 q ha hb
    | true =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263588 q = 1) (hb : d323713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263589 q = 1) (hb : d323714 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263589, d323714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263589, d323714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263590 q = 1) (hb : d323715 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263590, d323715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263590, d323715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263700 q = 1) (hb : d323716 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263700, d323716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263700, d323716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263701 q = 1) (hb : d323802 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263701, d323802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263701, d323802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98040 (p : Pattern) (ha : d263705 p = 1) (hb : d323806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263587 q = 1) (hb : d323712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98018 q ha hb
    | true =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263588 q = 1) (hb : d323713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263589 q = 1) (hb : d323714 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263589, d323714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263589, d323714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263590 q = 1) (hb : d323715 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263590, d323715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263590, d323715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263598 q = 1) (hb : d323718 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98019 q ha hb
    | true =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263599 q = 1) (hb : d323719 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263600 q = 1) (hb : d323720 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263600, d323720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263600, d323720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263601 q = 1) (hb : d323721 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263601, d323721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263601, d323721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263602 q = 1) (hb : d323722 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263602, d323722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263602, d323722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263621 q = 1) (hb : d323738 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263621, d323738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263621, d323738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263705 q = 1) (hb : d323806 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263705, d323806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263705, d323806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98041 (p : Pattern) (ha : d263711 p = 1) (hb : d323812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263702 q = 1) (hb : d323803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263702, d323803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98039 q ha hb
    | true =>
      simp only [d263702, d323803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98020 q ha hb
  have h2 (q : Pattern) (ha : d263703 q = 1) (hb : d323804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263703, d323804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263703, d323804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263704 q = 1) (hb : d323805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263704, d323805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263704, d323805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263706 q = 1) (hb : d323807 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263706, d323807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98020 q ha hb
    | true =>
      simp only [d263706, d323807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98040 q ha hb
  have h5 (q : Pattern) (ha : d263707 q = 1) (hb : d323808 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263707, d323808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263707, d323808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263708 q = 1) (hb : d323809 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263708, d323809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263708, d323809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263709 q = 1) (hb : d323810 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263709, d323810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263709, d323810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263623 q = 1) (hb : d323740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263623, d323740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98020 q ha hb
    | true =>
      simp only [d263623, d323740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98023 q ha hb
  have h9 (q : Pattern) (ha : d263624 q = 1) (hb : d323741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263624, d323741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263624, d323741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263625 q = 1) (hb : d323742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263625, d323742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263625, d323742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263638 q = 1) (hb : d323745 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263638, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98023 q ha hb
    | true =>
      simp only [d263638, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98025 q ha hb
  have h12 (q : Pattern) (ha : d263639 q = 1) (hb : d323746 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263639, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263639, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263640 q = 1) (hb : d323747 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263640, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263640, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263641 q = 1) (hb : d323748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263641, d323748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263641, d323748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d263710 q = 1) (hb : d323811 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263710, d323811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263710, d323811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d263711 q = 1) (hb : d323812 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263711, d323812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263711, d323812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro98042 (p : Pattern) (ha : d263716 p = 1) (hb : d323751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263623 q = 1) (hb : d323740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263623, d323740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98020 q ha hb
    | true =>
      simp only [d263623, d323740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98023 q ha hb
  have h2 (q : Pattern) (ha : d263624 q = 1) (hb : d323741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263624, d323741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263624, d323741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263625 q = 1) (hb : d323742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263625, d323742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263625, d323742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263638 q = 1) (hb : d323745 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263638, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98023 q ha hb
    | true =>
      simp only [d263638, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98025 q ha hb
  have h5 (q : Pattern) (ha : d263639 q = 1) (hb : d323746 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263639, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263639, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263640 q = 1) (hb : d323747 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263640, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263640, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263641 q = 1) (hb : d323748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263641, d323748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263641, d323748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263714 q = 1) (hb : d323749 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263714, d323749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263714, d323749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263715 q = 1) (hb : d323750 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263715, d323750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263715, d323750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263716 q = 1) (hb : d323751 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263716, d323751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263716, d323751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro98043 (p : Pattern) (ha : d263722 p = 1) (hb : d323818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263712 q = 1) (hb : d323813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263712, d323813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98041 q ha hb
    | true =>
      simp only [d263712, d323813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263713 q = 1) (hb : d323814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263713, d323814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263713, d323814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263717 q = 1) (hb : d323752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263717, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98042 q ha hb
    | true =>
      simp only [d263717, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263718 q = 1) (hb : d323753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263718, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263718, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263719 q = 1) (hb : d323815 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263719, d323815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263719, d323815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263720 q = 1) (hb : d323816 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263720, d323816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263720, d323816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263721 q = 1) (hb : d323817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263721, d323817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263721, d323817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263722 q = 1) (hb : d323818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263722, d323818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263722, d323818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98044 (p : Pattern) (ha : d263726 p = 1) (hb : d323761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263717 q = 1) (hb : d323752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263717, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98042 q ha hb
    | true =>
      simp only [d263717, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263718 q = 1) (hb : d323753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263718, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263718, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263723 q = 1) (hb : d323758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263723, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263723, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263724 q = 1) (hb : d323759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263724, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263724, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263725 q = 1) (hb : d323760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263725, d323760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263725, d323760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263726 q = 1) (hb : d323761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263726, d323761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263726, d323761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98045 (p : Pattern) (ha : d263732 p = 1) (hb : d323821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h3 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5243 q = 1) (hb : d69327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2061 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5244 q = 1) (hb : d69328 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5245 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d263732 q = 1) (hb : d323821 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263732, d323821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263732, d323821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro98046 (p : Pattern) (ha : d263738 p = 1) (hb : d323827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263611 q = 1) (hb : d323728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263611, d323728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98021 q ha hb
    | true =>
      simp only [d263611, d323728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263612 q = 1) (hb : d323729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263612, d323729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263612, d323729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263613 q = 1) (hb : d323730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263613, d323730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263613, d323730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263614 q = 1) (hb : d323731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263614, d323731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263614, d323731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263616 q = 1) (hb : d323733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98022 q ha hb
    | true =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263617 q = 1) (hb : d323734 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263618 q = 1) (hb : d323735 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263618, d323735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263618, d323735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263619 q = 1) (hb : d323736 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263619, d323736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263619, d323736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263620 q = 1) (hb : d323737 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263620, d323737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263620, d323737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263733 q = 1) (hb : d323822 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263733, d323822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98045 q ha hb
    | true =>
      simp only [d263733, d323822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263734 q = 1) (hb : d323823 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263734, d323823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263734, d323823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263735 q = 1) (hb : d323824 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263735, d323824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263735, d323824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263736 q = 1) (hb : d323825 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263736, d323825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263736, d323825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d263737 q = 1) (hb : d323826 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263737, d323826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263737, d323826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263738 q = 1) (hb : d323827 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263738, d323827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263738, d323827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98047 (p : Pattern) (ha : d263744 p = 1) (hb : d323828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53307 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5238 q = 1) (hb : d263739 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d263739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d263739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5239 q = 1) (hb : d263740 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d263740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5239, d263740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d207147 q = 1) (hb : d263741 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d207147, d263741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207147, d263741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d30103 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30103, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d207148 q = 1) (hb : d263742 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d207148, d263742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d207148, d263742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d207149 q = 1) (hb : d263743 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d207149, d263743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d207149, d263743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h13 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d5243 q = 1) (hb : d69327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h15 (q : Pattern) (ha : d2061 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h16 (q : Pattern) (ha : d5244 q = 1) (hb : d69328 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5245 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d263744 q = 1) (hb : d323828 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263744, d323828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d263744, d323828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  exact h18 p ha hb
theorem andIntro98048 (p : Pattern) (ha : d263750 p = 1) (hb : d323834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263745 q = 1) (hb : d323829 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263745, d323829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98047 q ha hb
    | true =>
      simp only [d263745, d323829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263746 q = 1) (hb : d323830 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263746, d323830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263746, d323830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263747 q = 1) (hb : d323831 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263747, d323831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263747, d323831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263748 q = 1) (hb : d323832 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263748, d323832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263748, d323832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263749 q = 1) (hb : d323833 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263749, d323833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263749, d323833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263750 q = 1) (hb : d323834 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263750, d323834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263750, d323834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98049 (p : Pattern) (ha : d263756 p = 1) (hb : d323840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263623 q = 1) (hb : d323740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263623, d323740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98020 q ha hb
    | true =>
      simp only [d263623, d323740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98023 q ha hb
  have h2 (q : Pattern) (ha : d263624 q = 1) (hb : d323741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263624, d323741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263624, d323741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263625 q = 1) (hb : d323742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263625, d323742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263625, d323742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263638 q = 1) (hb : d323745 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263638, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98023 q ha hb
    | true =>
      simp only [d263638, d323745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98025 q ha hb
  have h5 (q : Pattern) (ha : d263639 q = 1) (hb : d323746 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263639, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263639, d323746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263640 q = 1) (hb : d323747 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263640, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263640, d323747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263641 q = 1) (hb : d323748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263641, d323748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263641, d323748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263751 q = 1) (hb : d323835 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263751, d323835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98046 q ha hb
    | true =>
      simp only [d263751, d323835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98048 q ha hb
  have h9 (q : Pattern) (ha : d263752 q = 1) (hb : d323836 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263752, d323836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263752, d323836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263753 q = 1) (hb : d323837 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263753, d323837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263753, d323837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263754 q = 1) (hb : d323838 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263754, d323838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263754, d323838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263755 q = 1) (hb : d323839 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263755, d323839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263755, d323839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263756 q = 1) (hb : d323840 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263756, d323840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263756, d323840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro98050 (p : Pattern) (ha : d263762 p = 1) (hb : d323846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263757 q = 1) (hb : d323841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263757, d323841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98049 q ha hb
    | true =>
      simp only [d263757, d323841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263758 q = 1) (hb : d323842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263758, d323842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263758, d323842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263759 q = 1) (hb : d323843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263759, d323843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263759, d323843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263760 q = 1) (hb : d323844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263760, d323844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263760, d323844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263761 q = 1) (hb : d323845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263761, d323845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263761, d323845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263762 q = 1) (hb : d323846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263762, d323846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263762, d323846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98051 (p : Pattern) (ha : d263768 p = 1) (hb : d323852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263687 q = 1) (hb : d323789 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263687, d323789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98035 q ha hb
    | true =>
      simp only [d263687, d323789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98036 q ha hb
  have h2 (q : Pattern) (ha : d263688 q = 1) (hb : d323790 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263688, d323790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263688, d323790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263689 q = 1) (hb : d323791 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263689, d323791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263689, d323791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263690 q = 1) (hb : d323792 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263690, d323792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263690, d323792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263697 q = 1) (hb : d323799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263697, d323799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98037 q ha hb
    | true =>
      simp only [d263697, d323799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98038 q ha hb
  have h6 (q : Pattern) (ha : d263698 q = 1) (hb : d323800 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263698, d323800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263698, d323800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263699 q = 1) (hb : d323801 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263699, d323801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263699, d323801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263727 q = 1) (hb : d323819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263727, d323819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98043 q ha hb
    | true =>
      simp only [d263727, d323819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98044 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263664 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d263728 q = 1) (hb : d323820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263728, d323820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263728, d323820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d263763 q = 1) (hb : d323847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263763, d323847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98050 q ha hb
    | true =>
      simp only [d263763, d323847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263764 q = 1) (hb : d323848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263764, d323848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263764, d323848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263765 q = 1) (hb : d323849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263765, d323849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263765, d323849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263766 q = 1) (hb : d323850 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263766, d323850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263766, d323850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d263767 q = 1) (hb : d323851 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263767, d323851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263767, d323851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d263768 q = 1) (hb : d323852 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263768, d323852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263768, d323852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro98052 (p : Pattern) (ha : d263769 p = 1) (hb : d323853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d323752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98027 q ha hb
    | true =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d323753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d323758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263657 q = 1) (hb : d323759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263657, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263657, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263683 q = 1) (hb : d323785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263683, d323785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263683, d323785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263769 q = 1) (hb : d323853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263769, d323853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263769, d323853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98053 (p : Pattern) (ha : d263770 p = 1) (hb : d323854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d323762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263661 q = 1) (hb : d323763 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263661, d323763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263661, d323763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263685 q = 1) (hb : d323787 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263685, d323787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263685, d323787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263770 q = 1) (hb : d323854 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263770, d323854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263770, d323854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98054 (p : Pattern) (ha : d263775 p = 1) (hb : d323859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d323752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98027 q ha hb
    | true =>
      simp only [d263650, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d323753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d323758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263691 q = 1) (hb : d323793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263691, d323793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263691, d323793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263692 q = 1) (hb : d323794 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263692, d323794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263692, d323794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263775 q = 1) (hb : d323859 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263775, d323859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263775, d323859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98055 (p : Pattern) (ha : d263776 p = 1) (hb : d323860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d323762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d323762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263694 q = 1) (hb : d323796 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263694, d323796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263694, d323796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263695 q = 1) (hb : d323797 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263695, d323797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263695, d323797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263776 q = 1) (hb : d323860 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263776, d323860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263776, d323860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98056 (p : Pattern) (ha : d263780 p = 1) (hb : d323864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263712 q = 1) (hb : d323813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263712, d323813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98041 q ha hb
    | true =>
      simp only [d263712, d323813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263713 q = 1) (hb : d323814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263713, d323814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263713, d323814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263717 q = 1) (hb : d323752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263717, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98042 q ha hb
    | true =>
      simp only [d263717, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263718 q = 1) (hb : d323753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263718, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263718, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263719 q = 1) (hb : d323815 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263719, d323815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263719, d323815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263720 q = 1) (hb : d323816 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263720, d323816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263720, d323816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263721 q = 1) (hb : d323817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263721, d323817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263721, d323817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263780 q = 1) (hb : d323864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263780, d323864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263780, d323864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98057 (p : Pattern) (ha : d263781 p = 1) (hb : d323774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263717 q = 1) (hb : d323752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263717, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98042 q ha hb
    | true =>
      simp only [d263717, d323752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263718 q = 1) (hb : d323753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263718, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263718, d323753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d323756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98028 q ha hb
    | true =>
      simp only [d263654, d323756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d323757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d323757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263723 q = 1) (hb : d323758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263723, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263723, d323758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263724 q = 1) (hb : d323759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263724, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263724, d323759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263725 q = 1) (hb : d323760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263725, d323760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263725, d323760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263781 q = 1) (hb : d323774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263781, d323774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263781, d323774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98058 (p : Pattern) (ha : d263784 p = 1) (hb : d323867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263757 q = 1) (hb : d323841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263757, d323841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98049 q ha hb
    | true =>
      simp only [d263757, d323841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263758 q = 1) (hb : d323842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263758, d323842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263758, d323842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263759 q = 1) (hb : d323843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263759, d323843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263759, d323843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263760 q = 1) (hb : d323844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263760, d323844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263760, d323844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263761 q = 1) (hb : d323845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263761, d323845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263761, d323845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263784 q = 1) (hb : d323867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263784, d323867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263784, d323867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98059 (p : Pattern) (ha : d263790 p = 1) (hb : d323873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263687 q = 1) (hb : d323789 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263687, d323789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98035 q ha hb
    | true =>
      simp only [d263687, d323789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98036 q ha hb
  have h2 (q : Pattern) (ha : d263688 q = 1) (hb : d323790 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263688, d323790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263688, d323790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263689 q = 1) (hb : d323791 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263689, d323791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263689, d323791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263690 q = 1) (hb : d323792 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263690, d323792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263690, d323792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263697 q = 1) (hb : d323799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263697, d323799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98037 q ha hb
    | true =>
      simp only [d263697, d323799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98038 q ha hb
  have h6 (q : Pattern) (ha : d263698 q = 1) (hb : d323800 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263698, d323800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263698, d323800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263699 q = 1) (hb : d323801 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263699, d323801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263699, d323801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263727 q = 1) (hb : d323819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263727, d323819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98043 q ha hb
    | true =>
      simp only [d263727, d323819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98044 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263664 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d263728 q = 1) (hb : d323820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263728, d323820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263728, d323820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d263763 q = 1) (hb : d323847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263763, d323847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98050 q ha hb
    | true =>
      simp only [d263763, d323847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263764 q = 1) (hb : d323848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263764, d323848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263764, d323848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263765 q = 1) (hb : d323849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263765, d323849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263765, d323849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263766 q = 1) (hb : d323850 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263766, d323850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263766, d323850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d263767 q = 1) (hb : d323851 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263767, d323851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263767, d323851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d263771 q = 1) (hb : d323855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263771, d323855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98052 q ha hb
    | true =>
      simp only [d263771, d323855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98053 q ha hb
  have h17 (q : Pattern) (ha : d263772 q = 1) (hb : d323856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263772, d323856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263772, d323856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d263773 q = 1) (hb : d323857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263773, d323857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263773, d323857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d263774 q = 1) (hb : d323858 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263774, d323858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263774, d323858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d263777 q = 1) (hb : d323861 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263777, d323861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98054 q ha hb
    | true =>
      simp only [d263777, d323861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98055 q ha hb
  have h21 (q : Pattern) (ha : d263778 q = 1) (hb : d323862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263778, d323862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263778, d323862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d263779 q = 1) (hb : d323863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263779, d323863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d263779, d323863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d263782 q = 1) (hb : d323865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263782, d323865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98056 q ha hb
    | true =>
      simp only [d263782, d323865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98057 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d263674 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d263783 q = 1) (hb : d323866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263783, d323866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d263783, d323866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d263785 q = 1) (hb : d323868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263785, d323868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98058 q ha hb
    | true =>
      simp only [d263785, d323868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d263786 q = 1) (hb : d323869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263786, d323869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d263786, d323869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d263787 q = 1) (hb : d323870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263787, d323870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d263787, d323870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d263788 q = 1) (hb : d323871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263788, d323871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d263788, d323871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d263789 q = 1) (hb : d323872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263789, d323872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263789, d323872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d263790 q = 1) (hb : d323873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263790, d323873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263790, d323873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro98060 (p : Pattern) (ha : d263802 p = 1) (hb : d323880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263792 q = 1) (hb : d323766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263792, d323766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98044 q ha hb
    | true =>
      simp only [d263792, d323766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98030 q ha hb
  have h2 (q : Pattern) (ha : d263793 q = 1) (hb : d323767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263793, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263793, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263794 q = 1) (hb : d323768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263794, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263794, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263795 q = 1) (hb : d323769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263795, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263795, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263796 q = 1) (hb : d323770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263796, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263796, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263797 q = 1) (hb : d323875 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263797, d323875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98030 q ha hb
    | true =>
      simp only [d263797, d323875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263798 q = 1) (hb : d323876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263798, d323876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263798, d323876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263799 q = 1) (hb : d323877 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263799, d323877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263799, d323877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263800 q = 1) (hb : d323878 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263800, d323878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263800, d323878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263801 q = 1) (hb : d323879 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263801, d323879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263801, d323879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263802 q = 1) (hb : d323880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263802, d323880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263802, d323880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98061 (p : Pattern) (ha : d263808 p = 1) (hb : d323886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263797 q = 1) (hb : d323875 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263797, d323875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98030 q ha hb
    | true =>
      simp only [d263797, d323875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263798 q = 1) (hb : d323876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263798, d323876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263798, d323876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263799 q = 1) (hb : d323877 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263799, d323877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263799, d323877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263800 q = 1) (hb : d323878 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263800, d323878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263800, d323878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263801 q = 1) (hb : d323879 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263801, d323879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263801, d323879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263803 q = 1) (hb : d323881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263803, d323881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98033 q ha hb
    | true =>
      simp only [d263803, d323881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263804 q = 1) (hb : d323882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263804, d323882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263804, d323882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263805 q = 1) (hb : d323883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263805, d323883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263805, d323883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263806 q = 1) (hb : d323884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263806, d323884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263806, d323884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263807 q = 1) (hb : d323885 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263807, d323885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263807, d323885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263808 q = 1) (hb : d323886 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263808, d323886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263808, d323886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98062 (p : Pattern) (ha : d263815 p = 1) (hb : d323893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263782 q = 1) (hb : d323865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263782, d323865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98056 q ha hb
    | true =>
      simp only [d263782, d323865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98057 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263783 q = 1) (hb : d323866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263783, d323866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263783, d323866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d263785 q = 1) (hb : d323868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263785, d323868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98058 q ha hb
    | true =>
      simp only [d263785, d323868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263786 q = 1) (hb : d323869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263786, d323869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263786, d323869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263787 q = 1) (hb : d323870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263787, d323870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263787, d323870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263813 q = 1) (hb : d323891 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263813, d323891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263813, d323891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263814 q = 1) (hb : d323892 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263814, d323892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263814, d323892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263815 q = 1) (hb : d323893 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263815, d323893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263815, d323893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro98063 (p : Pattern) (ha : d263817 p = 1) (hb : d323895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263803 q = 1) (hb : d323881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263803, d323881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98033 q ha hb
    | true =>
      simp only [d263803, d323881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263804 q = 1) (hb : d323882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263804, d323882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263804, d323882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263805 q = 1) (hb : d323883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263805, d323883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263805, d323883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263806 q = 1) (hb : d323884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263806, d323884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263806, d323884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263807 q = 1) (hb : d323885 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263807, d323885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263807, d323885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263817 q = 1) (hb : d323895 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263817, d323895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263817, d323895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98064 (p : Pattern) (ha : d263828 p = 1) (hb : d323906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263823 q = 1) (hb : d323901 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263823, d323901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263823, d323901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98018 q ha hb
  have h2 (q : Pattern) (ha : d263587 q = 1) (hb : d323712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98018 q ha hb
    | true =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263824 q = 1) (hb : d323902 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263824, d323902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263824, d323902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263588 q = 1) (hb : d323713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263825 q = 1) (hb : d323903 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263825, d323903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263825, d323903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263826 q = 1) (hb : d323904 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263826, d323904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263826, d323904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263827 q = 1) (hb : d323905 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263827, d323905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263827, d323905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263828 q = 1) (hb : d323906 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263828, d323906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263828, d323906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98065 (p : Pattern) (ha : d263843 p = 1) (hb : d323912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263833 q = 1) (hb : d323901 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263833, d323901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263833, d323901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98017 q ha hb
  have h3 (q : Pattern) (ha : d263581 q = 1) (hb : d323712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263581, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98017 q ha hb
    | true =>
      simp only [d263581, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d263834 q = 1) (hb : d323902 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263834, d323902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263834, d323902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263582 q = 1) (hb : d323713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263582, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263582, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d263835 q = 1) (hb : d323903 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263835, d323903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263835, d323903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263836 q = 1) (hb : d323904 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263836, d323904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263836, d323904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d263837 q = 1) (hb : d323905 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263837, d323905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263837, d323905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263823 q = 1) (hb : d323901 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263823, d323901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263823, d323901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98018 q ha hb
  have h10 (q : Pattern) (ha : d263587 q = 1) (hb : d323712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98018 q ha hb
    | true =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d263824 q = 1) (hb : d323902 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263824, d323902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263824, d323902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263588 q = 1) (hb : d323713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d263825 q = 1) (hb : d323903 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263825, d323903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263825, d323903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263826 q = 1) (hb : d323904 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263826, d323904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263826, d323904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d263838 q = 1) (hb : d323907 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263838, d323907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263838, d323907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98019 q ha hb
  have h16 (q : Pattern) (ha : d263598 q = 1) (hb : d323718 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98019 q ha hb
    | true =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h17 (q : Pattern) (ha : d263839 q = 1) (hb : d323908 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263839, d323908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263839, d323908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d263599 q = 1) (hb : d323719 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h19 (q : Pattern) (ha : d263840 q = 1) (hb : d323909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263840, d323909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263840, d323909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d263841 q = 1) (hb : d323910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263841, d323910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263841, d323910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h21 (q : Pattern) (ha : d263842 q = 1) (hb : d323911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263842, d323911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263842, d323911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d263843 q = 1) (hb : d323912 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263843, d323912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263843, d323912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro98066 (p : Pattern) (ha : d263848 p = 1) (hb : d323917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263823 q = 1) (hb : d323901 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263823, d323901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263823, d323901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98018 q ha hb
  have h2 (q : Pattern) (ha : d263587 q = 1) (hb : d323712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98018 q ha hb
    | true =>
      simp only [d263587, d323712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263824 q = 1) (hb : d323902 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263824, d323902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263824, d323902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263588 q = 1) (hb : d323713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263588, d323713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263825 q = 1) (hb : d323903 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263825, d323903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263825, d323903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263826 q = 1) (hb : d323904 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263826, d323904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263826, d323904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263838 q = 1) (hb : d323907 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263838, d323907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263838, d323907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98019 q ha hb
  have h8 (q : Pattern) (ha : d263598 q = 1) (hb : d323718 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98019 q ha hb
    | true =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263839 q = 1) (hb : d323908 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263839, d323908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263839, d323908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263599 q = 1) (hb : d323719 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263840 q = 1) (hb : d323909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263840, d323909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263840, d323909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263841 q = 1) (hb : d323910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263841, d323910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263841, d323910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263842 q = 1) (hb : d323911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263842, d323911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263842, d323911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263847 q = 1) (hb : d323916 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263847, d323916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263847, d323916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263848 q = 1) (hb : d323917 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263848, d323917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263848, d323917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98067 (p : Pattern) (ha : d263862 p = 1) (hb : d323931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263853 q = 1) (hb : d323922 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263853, d323922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263853, d323922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98021 q ha hb
  have h2 (q : Pattern) (ha : d263611 q = 1) (hb : d323728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263611, d323728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98021 q ha hb
    | true =>
      simp only [d263611, d323728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263854 q = 1) (hb : d323923 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263854, d323923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263854, d323923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263612 q = 1) (hb : d323729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263612, d323729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263612, d323729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263855 q = 1) (hb : d323924 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263855, d323924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263855, d323924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263856 q = 1) (hb : d323925 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263856, d323925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263856, d323925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263857 q = 1) (hb : d323926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263857, d323926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263857, d323926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98022 q ha hb
  have h8 (q : Pattern) (ha : d263616 q = 1) (hb : d323733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98022 q ha hb
    | true =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263858 q = 1) (hb : d323927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263858, d323927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263858, d323927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263617 q = 1) (hb : d323734 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263859 q = 1) (hb : d323928 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263859, d323928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263859, d323928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263860 q = 1) (hb : d323929 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263860, d323929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263860, d323929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263861 q = 1) (hb : d323930 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263861, d323930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263861, d323930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263838 q = 1) (hb : d323907 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263838, d323907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263838, d323907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98019 q ha hb
  have h15 (q : Pattern) (ha : d263598 q = 1) (hb : d323718 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98019 q ha hb
    | true =>
      simp only [d263598, d323718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d263839 q = 1) (hb : d323908 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263839, d323908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263839, d323908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263599 q = 1) (hb : d323719 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263599, d323719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d263840 q = 1) (hb : d323909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263840, d323909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263840, d323909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d263841 q = 1) (hb : d323910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263841, d323910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d263841, d323910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d263847 q = 1) (hb : d323916 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263847, d323916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263847, d323916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d263862 q = 1) (hb : d323931 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263862, d323931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263862, d323931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro98068 (p : Pattern) (ha : d263871 p = 1) (hb : d323936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263866 q = 1) (hb : d323926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263866, d323926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263866, d323926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98024 q ha hb
  have h2 (q : Pattern) (ha : d263632 q = 1) (hb : d323733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263632, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98024 q ha hb
    | true =>
      simp only [d263632, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263867 q = 1) (hb : d323927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263867, d323927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263867, d323927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263633 q = 1) (hb : d323734 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263633, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263633, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263868 q = 1) (hb : d323928 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263868, d323928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263868, d323928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263869 q = 1) (hb : d323929 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263869, d323929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263869, d323929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263870 q = 1) (hb : d323935 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263870, d323935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263870, d323935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d263871 q = 1) (hb : d323936 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263871, d323936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263871, d323936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro98069 (p : Pattern) (ha : d263877 p = 1) (hb : d323942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263844 q = 1) (hb : d323913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263844, d323913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98064 q ha hb
    | true =>
      simp only [d263844, d323913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98065 q ha hb
  have h2 (q : Pattern) (ha : d263845 q = 1) (hb : d323914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263845, d323914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263845, d323914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263846 q = 1) (hb : d323915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263846, d323915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263846, d323915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263849 q = 1) (hb : d323918 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263849, d323918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98065 q ha hb
    | true =>
      simp only [d263849, d323918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98066 q ha hb
  have h5 (q : Pattern) (ha : d263850 q = 1) (hb : d323919 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263850, d323919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263850, d323919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263851 q = 1) (hb : d323920 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263851, d323920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263851, d323920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263852 q = 1) (hb : d323921 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263852, d323921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263852, d323921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263863 q = 1) (hb : d323932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263863, d323932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98065 q ha hb
    | true =>
      simp only [d263863, d323932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98067 q ha hb
  have h9 (q : Pattern) (ha : d263864 q = 1) (hb : d323933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263864, d323933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263864, d323933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263865 q = 1) (hb : d323934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263865, d323934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263865, d323934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263872 q = 1) (hb : d323937 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263872, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98067 q ha hb
    | true =>
      simp only [d263872, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98068 q ha hb
  have h12 (q : Pattern) (ha : d263873 q = 1) (hb : d323938 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263873, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263873, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263874 q = 1) (hb : d323939 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263874, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263874, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263875 q = 1) (hb : d323940 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263875, d323940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263875, d323940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d263876 q = 1) (hb : d323941 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263876, d323941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263876, d323941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d263877 q = 1) (hb : d323942 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263877, d323942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263877, d323942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro98070 (p : Pattern) (ha : d263882 p = 1) (hb : d323947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263863 q = 1) (hb : d323932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263863, d323932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98065 q ha hb
    | true =>
      simp only [d263863, d323932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98067 q ha hb
  have h2 (q : Pattern) (ha : d263864 q = 1) (hb : d323933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263864, d323933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263864, d323933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263865 q = 1) (hb : d323934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263865, d323934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263865, d323934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263872 q = 1) (hb : d323937 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263872, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98067 q ha hb
    | true =>
      simp only [d263872, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98068 q ha hb
  have h5 (q : Pattern) (ha : d263873 q = 1) (hb : d323938 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263873, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263873, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263874 q = 1) (hb : d323939 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263874, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263874, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263875 q = 1) (hb : d323940 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263875, d323940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263875, d323940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263880 q = 1) (hb : d323945 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263880, d323945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263880, d323945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263881 q = 1) (hb : d323946 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263881, d323946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263881, d323946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263882 q = 1) (hb : d323947 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263882, d323947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263882, d323947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro98071 (p : Pattern) (ha : d263888 p = 1) (hb : d323953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263878 q = 1) (hb : d323943 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263878, d323943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98069 q ha hb
    | true =>
      simp only [d263878, d323943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263879 q = 1) (hb : d323944 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263879, d323944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263879, d323944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263883 q = 1) (hb : d323948 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263883, d323948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98070 q ha hb
    | true =>
      simp only [d263883, d323948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263884 q = 1) (hb : d323949 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263884, d323949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263884, d323949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263885 q = 1) (hb : d323950 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263885, d323950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263885, d323950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263886 q = 1) (hb : d323951 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263886, d323951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263886, d323951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263887 q = 1) (hb : d323952 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263887, d323952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263887, d323952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263888 q = 1) (hb : d323953 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263888, d323953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263888, d323953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98072 (p : Pattern) (ha : d263890 p = 1) (hb : d323936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263857 q = 1) (hb : d323926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263857, d323926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263857, d323926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98022 q ha hb
  have h2 (q : Pattern) (ha : d263616 q = 1) (hb : d323733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98022 q ha hb
    | true =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263858 q = 1) (hb : d323927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263858, d323927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263858, d323927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263617 q = 1) (hb : d323734 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263859 q = 1) (hb : d323928 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263859, d323928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263859, d323928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263860 q = 1) (hb : d323929 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263860, d323929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263860, d323929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263889 q = 1) (hb : d323935 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263889, d323935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263889, d323935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d263890 q = 1) (hb : d323936 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263890, d323936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263890, d323936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro98073 (p : Pattern) (ha : d263896 p = 1) (hb : d323955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263891 q = 1) (hb : d323937 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263891, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98067 q ha hb
    | true =>
      simp only [d263891, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98072 q ha hb
  have h2 (q : Pattern) (ha : d263892 q = 1) (hb : d323938 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263892, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263892, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263893 q = 1) (hb : d323939 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263893, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263893, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263894 q = 1) (hb : d323945 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263894, d323945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263894, d323945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263895 q = 1) (hb : d323954 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263895, d323954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263895, d323954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263896 q = 1) (hb : d323955 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263896, d323955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263896, d323955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98074 (p : Pattern) (ha : d263902 p = 1) (hb : d323961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263883 q = 1) (hb : d323948 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263883, d323948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98070 q ha hb
    | true =>
      simp only [d263883, d323948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263884 q = 1) (hb : d323949 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263884, d323949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263884, d323949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263897 q = 1) (hb : d323956 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263897, d323956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98073 q ha hb
    | true =>
      simp only [d263897, d323956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263898 q = 1) (hb : d323957 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263898, d323957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263898, d323957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263899 q = 1) (hb : d323958 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263899, d323958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263899, d323958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263900 q = 1) (hb : d323959 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263900, d323959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263900, d323959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263901 q = 1) (hb : d323960 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263901, d323960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263901, d323960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263902 q = 1) (hb : d323961 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263902, d323961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263902, d323961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98075 (p : Pattern) (ha : d263948 p = 1) (hb : d323969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263853 q = 1) (hb : d323922 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263853, d323922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263853, d323922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98021 q ha hb
  have h2 (q : Pattern) (ha : d263611 q = 1) (hb : d323728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263611, d323728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98021 q ha hb
    | true =>
      simp only [d263611, d323728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263854 q = 1) (hb : d323923 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263854, d323923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263854, d323923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263612 q = 1) (hb : d323729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263612, d323729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263612, d323729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263855 q = 1) (hb : d323924 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263855, d323924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263855, d323924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263856 q = 1) (hb : d323925 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263856, d323925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263856, d323925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263857 q = 1) (hb : d323926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263857, d323926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263857, d323926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98022 q ha hb
  have h8 (q : Pattern) (ha : d263616 q = 1) (hb : d323733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98022 q ha hb
    | true =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263858 q = 1) (hb : d323927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263858, d323927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263858, d323927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263617 q = 1) (hb : d323734 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263859 q = 1) (hb : d323928 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263859, d323928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263859, d323928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263860 q = 1) (hb : d323929 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263860, d323929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263860, d323929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263861 q = 1) (hb : d323930 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263861, d323930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263861, d323930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263943 q = 1) (hb : d323964 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263943, d323964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263943, d323964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98045 q ha hb
  have h15 (q : Pattern) (ha : d263733 q = 1) (hb : d323822 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263733, d323822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98045 q ha hb
    | true =>
      simp only [d263733, d323822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d263944 q = 1) (hb : d323965 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263944, d323965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263944, d323965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263734 q = 1) (hb : d323823 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263734, d323823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263734, d323823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d263945 q = 1) (hb : d323966 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263945, d323966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263945, d323966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d263946 q = 1) (hb : d323967 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263946, d323967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d263946, d323967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d263947 q = 1) (hb : d323968 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263947, d323968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263947, d323968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d263948 q = 1) (hb : d323969 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263948, d323969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263948, d323969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro98076 (p : Pattern) (ha : d263954 p = 1) (hb : d323975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263949 q = 1) (hb : d323970 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263949, d323970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263949, d323970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98047 q ha hb
  have h2 (q : Pattern) (ha : d263745 q = 1) (hb : d323829 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263745, d323829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98047 q ha hb
    | true =>
      simp only [d263745, d323829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263950 q = 1) (hb : d323971 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263950, d323971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263950, d323971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263746 q = 1) (hb : d323830 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263746, d323830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263746, d323830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263951 q = 1) (hb : d323972 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263951, d323972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263951, d323972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263952 q = 1) (hb : d323973 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263952, d323973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263952, d323973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263953 q = 1) (hb : d323974 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263953, d323974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263953, d323974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263954 q = 1) (hb : d323975 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263954, d323975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263954, d323975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98077 (p : Pattern) (ha : d263960 p = 1) (hb : d323981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263863 q = 1) (hb : d323932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263863, d323932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98065 q ha hb
    | true =>
      simp only [d263863, d323932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98067 q ha hb
  have h2 (q : Pattern) (ha : d263864 q = 1) (hb : d323933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263864, d323933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263864, d323933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263865 q = 1) (hb : d323934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263865, d323934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263865, d323934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263872 q = 1) (hb : d323937 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263872, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98067 q ha hb
    | true =>
      simp only [d263872, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98068 q ha hb
  have h5 (q : Pattern) (ha : d263873 q = 1) (hb : d323938 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263873, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263873, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263874 q = 1) (hb : d323939 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263874, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263874, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263875 q = 1) (hb : d323940 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263875, d323940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263875, d323940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263955 q = 1) (hb : d323976 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263955, d323976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98075 q ha hb
    | true =>
      simp only [d263955, d323976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98076 q ha hb
  have h9 (q : Pattern) (ha : d263956 q = 1) (hb : d323977 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263956, d323977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263956, d323977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263957 q = 1) (hb : d323978 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263957, d323978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263957, d323978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263958 q = 1) (hb : d323979 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263958, d323979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263958, d323979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263959 q = 1) (hb : d323980 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263959, d323980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263959, d323980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263960 q = 1) (hb : d323981 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263960, d323981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263960, d323981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro98078 (p : Pattern) (ha : d263966 p = 1) (hb : d323987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263961 q = 1) (hb : d323982 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263961, d323982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98077 q ha hb
    | true =>
      simp only [d263961, d323982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263962 q = 1) (hb : d323983 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263962, d323983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263962, d323983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263963 q = 1) (hb : d323984 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263963, d323984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263963, d323984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263964 q = 1) (hb : d323985 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263964, d323985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263964, d323985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263965 q = 1) (hb : d323986 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263965, d323986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263965, d323986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263966 q = 1) (hb : d323987 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263966, d323987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263966, d323987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98079 (p : Pattern) (ha : d263972 p = 1) (hb : d323993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263903 q = 1) (hb : d323962 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263903, d323962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98071 q ha hb
    | true =>
      simp only [d263903, d323962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98074 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263941 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263942 q = 1) (hb : d323963 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263942, d323963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263942, d323963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d263967 q = 1) (hb : d323988 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263967, d323988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98078 q ha hb
    | true =>
      simp only [d263967, d323988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263968 q = 1) (hb : d323989 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263968, d323989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263968, d323989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263969 q = 1) (hb : d323990 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263969, d323990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263969, d323990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263970 q = 1) (hb : d323991 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263970, d323991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263970, d323991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263971 q = 1) (hb : d323992 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263971, d323992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263971, d323992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263972 q = 1) (hb : d323993 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263972, d323993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263972, d323993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro98080 (p : Pattern) (ha : d263977 p = 1) (hb : d323998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263897 q = 1) (hb : d323956 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263897, d323956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98073 q ha hb
    | true =>
      simp only [d263897, d323956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263898 q = 1) (hb : d323957 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263898, d323957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263898, d323957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263974 q = 1) (hb : d323995 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263974, d323995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263974, d323995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263975 q = 1) (hb : d323996 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263975, d323996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263975, d323996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263976 q = 1) (hb : d323997 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263976, d323997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263976, d323997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263977 q = 1) (hb : d323998 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263977, d323998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263977, d323998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98081 (p : Pattern) (ha : d263983 p = 1) (hb : d324004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263978 q = 1) (hb : d323999 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263978, d323999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98080 q ha hb
    | true =>
      simp only [d263978, d323999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263979 q = 1) (hb : d324000 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263979, d324000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263979, d324000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263980 q = 1) (hb : d324001 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263980, d324001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263980, d324001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263981 q = 1) (hb : d324002 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263981, d324002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263981, d324002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263982 q = 1) (hb : d324003 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263982, d324003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263982, d324003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263983 q = 1) (hb : d324004 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263983, d324004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263983, d324004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98082 (p : Pattern) (ha : d263989 p = 1) (hb : d324010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263670 q = 1) (hb : d323772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263670, d323772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263670, d323772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98031 q ha hb
  have h2 (q : Pattern) (ha : d263671 q = 1) (hb : d323773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263671, d323773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263671, d323773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263680 q = 1) (hb : d323782 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263680, d323782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98031 q ha hb
    | true =>
      simp only [d263680, d323782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98034 q ha hb
  have h4 (q : Pattern) (ha : d263681 q = 1) (hb : d323783 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263681, d323783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263681, d323783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263682 q = 1) (hb : d323784 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263682, d323784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263682, d323784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263791 q = 1) (hb : d323874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263791, d323874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98051 q ha hb
    | true =>
      simp only [d263791, d323874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98059 q ha hb
  have h7 (q : Pattern) (ha : d263809 q = 1) (hb : d323887 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263809, d323887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98060 q ha hb
    | true =>
      simp only [d263809, d323887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98061 q ha hb
  have h8 (q : Pattern) (ha : d263810 q = 1) (hb : d323888 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263810, d323888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263810, d323888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263811 q = 1) (hb : d323889 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263811, d323889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263811, d323889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d263812 q = 1) (hb : d323890 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263812, d323890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263812, d323890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263816 q = 1) (hb : d323894 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263816, d323894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263816, d323894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98062 q ha hb
  have h12 (q : Pattern) (ha : d263818 q = 1) (hb : d323896 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263818, d323896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263818, d323896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98063 q ha hb
  have h13 (q : Pattern) (ha : d263819 q = 1) (hb : d323897 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263819, d323897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263819, d323897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263820 q = 1) (hb : d323898 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263820, d323898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263820, d323898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263821 q = 1) (hb : d323899 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263821, d323899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263821, d323899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d263822 q = 1) (hb : d323900 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263822, d323900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263822, d323900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263973 q = 1) (hb : d323994 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263973, d323994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263973, d323994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98079 q ha hb
  have h18 (q : Pattern) (ha : d263984 q = 1) (hb : d324005 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263984, d324005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263984, d324005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98081 q ha hb
  have h19 (q : Pattern) (ha : d263985 q = 1) (hb : d324006 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263985, d324006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263985, d324006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d263986 q = 1) (hb : d324007 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263986, d324007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263986, d324007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d263987 q = 1) (hb : d324008 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263987, d324008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d263987, d324008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d263988 q = 1) (hb : d324009 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263988, d324009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d263988, d324009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d263989 q = 1) (hb : d324010 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263989, d324010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263989, d324010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro98083 (p : Pattern) (ha : d263995 p = 1) (hb : d324016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263990 q = 1) (hb : d324011 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263990, d324011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263990, d324011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98082 q ha hb
  have h2 (q : Pattern) (ha : d263991 q = 1) (hb : d324012 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263991, d324012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263991, d324012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263992 q = 1) (hb : d324013 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263992, d324013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263992, d324013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263993 q = 1) (hb : d324014 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263993, d324014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263993, d324014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263994 q = 1) (hb : d324015 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263994, d324015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263994, d324015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263995 q = 1) (hb : d324016 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263995, d324016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263995, d324016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98084 (p : Pattern) (ha : d264001 p = 1) (hb : d324022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d262468 q = 1) (hb : d322731 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262468, d322731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97785 q ha hb
    | true =>
      simp only [d262468, d322731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97832 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262753 q = 1) (hb : d323005 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262753, d323005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262753, d323005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97887 q ha hb
  have h3 (q : Pattern) (ha : d262754 q = 1) (hb : d323006 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d262754, d323006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d262754, d323006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263147 q = 1) (hb : d323347 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263147, d323347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263147, d323347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97950 q ha hb
  have h5 (q : Pattern) (ha : d263148 q = 1) (hb : d323348 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263148, d323348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263148, d323348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263149 q = 1) (hb : d323349 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263149, d323349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263149, d323349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263557 q = 1) (hb : d323704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263557, d323704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263557, d323704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98016 q ha hb
  have h8 (q : Pattern) (ha : d263558 q = 1) (hb : d323705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263558, d323705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263558, d323705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263559 q = 1) (hb : d323706 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263559, d323706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263559, d323706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263560 q = 1) (hb : d323707 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263560, d323707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263560, d323707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263996 q = 1) (hb : d324017 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263996, d324017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263996, d324017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98083 q ha hb
  have h12 (q : Pattern) (ha : d263997 q = 1) (hb : d324018 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263997, d324018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263997, d324018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263998 q = 1) (hb : d324019 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263998, d324019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263998, d324019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263999 q = 1) (hb : d324020 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263999, d324020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263999, d324020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d264000 q = 1) (hb : d324021 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d264000, d324021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d264000, d324021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d264001 q = 1) (hb : d324022 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d264001, d324022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d264001, d324022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro98085 (p : Pattern) (ha : d264007 p = 1) (hb : d324028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264002 q = 1) (hb : d324023 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d264002, d324023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98084 q ha hb
    | true =>
      simp only [d264002, d324023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264003 q = 1) (hb : d324024 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d264003, d324024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264003, d324024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264004 q = 1) (hb : d324025 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d264004, d324025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264004, d324025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264005 q = 1) (hb : d324026 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d264005, d324026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264005, d324026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264006 q = 1) (hb : d324027 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d264006, d324027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264006, d324027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264007 q = 1) (hb : d324028 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d264007, d324028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264007, d324028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98086 (p : Pattern) (ha : d264013 p = 1) (hb : d324034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264008 q = 1) (hb : d324029 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d264008, d324029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98085 q ha hb
    | true =>
      simp only [d264008, d324029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264009 q = 1) (hb : d324030 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d264009, d324030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264009, d324030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264010 q = 1) (hb : d324031 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d264010, d324031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264010, d324031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264011 q = 1) (hb : d324032 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d264011, d324032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264011, d324032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264012 q = 1) (hb : d324033 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d264012, d324033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264012, d324033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264013 q = 1) (hb : d324034 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d264013, d324034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264013, d324034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98087 (p : Pattern) (ha : d264019 p = 1) (hb : d324040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264014 q = 1) (hb : d324035 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d264014, d324035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98086 q ha hb
    | true =>
      simp only [d264014, d324035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264015 q = 1) (hb : d324036 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d264015, d324036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264015, d324036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264016 q = 1) (hb : d324037 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d264016, d324037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264016, d324037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264017 q = 1) (hb : d324038 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d264017, d324038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264017, d324038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264018 q = 1) (hb : d324039 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d264018, d324039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264018, d324039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264019 q = 1) (hb : d324040 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d264019, d324040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264019, d324040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98088 (p : Pattern) (ha : d264025 p = 1) (hb : d324046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264020 q = 1) (hb : d324041 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d264020, d324041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98087 q ha hb
    | true =>
      simp only [d264020, d324041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264021 q = 1) (hb : d324042 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d264021, d324042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264021, d324042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264022 q = 1) (hb : d324043 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d264022, d324043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264022, d324043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264023 q = 1) (hb : d324044 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d264023, d324044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264023, d324044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264024 q = 1) (hb : d324045 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d264024, d324045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264024, d324045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264025 q = 1) (hb : d324046 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d264025, d324046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264025, d324046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98089 (p : Pattern) (ha : d264031 p = 1) (hb : d324052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264026 q = 1) (hb : d324047 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d264026, d324047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98088 q ha hb
    | true =>
      simp only [d264026, d324047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264027 q = 1) (hb : d324048 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d264027, d324048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264027, d324048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264028 q = 1) (hb : d324049 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d264028, d324049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264028, d324049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264029 q = 1) (hb : d324050 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d264029, d324050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264029, d324050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264030 q = 1) (hb : d324051 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d264030, d324051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264030, d324051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264031 q = 1) (hb : d324052 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d264031, d324052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264031, d324052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98090 (p : Pattern) (ha : d264037 p = 1) (hb : d324058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264032 q = 1) (hb : d324053 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d264032, d324053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98089 q ha hb
    | true =>
      simp only [d264032, d324053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264033 q = 1) (hb : d324054 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d264033, d324054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264033, d324054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264034 q = 1) (hb : d324055 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d264034, d324055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264034, d324055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264035 q = 1) (hb : d324056 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d264035, d324056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264035, d324056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264036 q = 1) (hb : d324057 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d264036, d324057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264036, d324057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264037 q = 1) (hb : d324058 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d264037, d324058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264037, d324058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98091 (p : Pattern) (ha : d264043 p = 1) (hb : d324064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264038 q = 1) (hb : d324059 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d264038, d324059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98090 q ha hb
    | true =>
      simp only [d264038, d324059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264039 q = 1) (hb : d324060 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d264039, d324060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264039, d324060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264040 q = 1) (hb : d324061 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d264040, d324061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264040, d324061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264041 q = 1) (hb : d324062 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d264041, d324062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264041, d324062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264042 q = 1) (hb : d324063 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d264042, d324063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264042, d324063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264043 q = 1) (hb : d324064 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d264043, d324064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264043, d324064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98092 (p : Pattern) (ha : d290066 p = 1) (hb : d322255 p = 1) : d324067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d322255 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40183 q = 1) (hb : d322255 q = 1) : d322288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40183, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97475 q ha hb
    | true =>
      simp only [d40183, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40243 q = 1) (hb : d322255 q = 1) : d322348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40243, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40243, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40244 q = 1) (hb : d322255 q = 1) : d322349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40244, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40244, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40245 q = 1) (hb : d322255 q = 1) : d322350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40245, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40245, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40246 q = 1) (hb : d322255 q = 1) : d322351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40246, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40246, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290066 q = 1) (hb : d322255 q = 1) : d324067 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290066, d324067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290066, d324067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro98093 (p : Pattern) (ha : d290076 p = 1) (hb : d322255 p = 1) : d324077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d322255 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d40219 q = 1) (hb : d322255 q = 1) : d322324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40219, d322324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97480 q ha hb
    | true =>
      simp only [d40219, d322324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290072 q = 1) (hb : d322255 q = 1) : d324073 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290072, d324073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290072, d324073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290073 q = 1) (hb : d322255 q = 1) : d324074 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290073, d324074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290073, d324074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290074 q = 1) (hb : d322255 q = 1) : d324075 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290074, d324075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290074, d324075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290075 q = 1) (hb : d322255 q = 1) : d324076 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290075, d324076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290075, d324076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290076 q = 1) (hb : d322255 q = 1) : d324077 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290076, d324077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290076, d324077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro98094 (p : Pattern) (ha : d290082 p = 1) (hb : d322255 p = 1) : d324083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40248 q = 1) (hb : d322255 q = 1) : d322353 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40248, d322353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97483 q ha hb
    | true =>
      simp only [d40248, d322353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97484 q ha hb
  have h2 (q : Pattern) (ha : d40249 q = 1) (hb : d322255 q = 1) : d322354 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40249, d322354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40249, d322354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290064 q = 1) (hb : d322255 q = 1) : d324065 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290064, d324065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290064, d324065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290065 q = 1) (hb : d322255 q = 1) : d324066 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290065, d324066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290065, d324066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290067 q = 1) (hb : d322255 q = 1) : d324068 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290067, d324068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290067, d324068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98092 q ha hb
  have h6 (q : Pattern) (ha : d290068 q = 1) (hb : d322255 q = 1) : d324069 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290068, d324069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290068, d324069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d290069 q = 1) (hb : d322255 q = 1) : d324070 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290069, d324070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290069, d324070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d290070 q = 1) (hb : d322255 q = 1) : d324071 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290070, d324071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290070, d324071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d290071 q = 1) (hb : d322255 q = 1) : d324072 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290071, d324072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290071, d324072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290077 q = 1) (hb : d322255 q = 1) : d324078 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290077, d324078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290077, d324078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98093 q ha hb
  have h11 (q : Pattern) (ha : d290078 q = 1) (hb : d322255 q = 1) : d324079 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290078, d324079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290078, d324079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d290079 q = 1) (hb : d322255 q = 1) : d324080 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290079, d324080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290079, d324080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d290080 q = 1) (hb : d322255 q = 1) : d324081 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290080, d324081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290080, d324081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d290081 q = 1) (hb : d322255 q = 1) : d324082 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290081, d324082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290081, d324082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d290082 q = 1) (hb : d322255 q = 1) : d324083 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290082, d324083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290082, d324083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98095 (p : Pattern) (ha : d290088 p = 1) (hb : d322255 p = 1) : d324089 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d322255 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d290083 q = 1) (hb : d322255 q = 1) : d324084 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290083, d324084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290083, d324084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98094 q ha hb
  have h3 (q : Pattern) (ha : d290084 q = 1) (hb : d322255 q = 1) : d324085 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290084, d324085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290084, d324085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290085 q = 1) (hb : d322255 q = 1) : d324086 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290085, d324086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290085, d324086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290086 q = 1) (hb : d322255 q = 1) : d324087 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290086, d324087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290086, d324087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290087 q = 1) (hb : d322255 q = 1) : d324088 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290087, d324088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290087, d324088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290088 q = 1) (hb : d322255 q = 1) : d324089 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290088, d324089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290088, d324089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro98096 (p : Pattern) (ha : d290091 p = 1) (hb : d322255 p = 1) : d324092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40465 q = 1) (hb : d322255 q = 1) : d322520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40465, d322520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97514 q ha hb
    | true =>
      simp only [d40465, d322520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97515 q ha hb
  have h2 (q : Pattern) (ha : d40466 q = 1) (hb : d322255 q = 1) : d322521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40466, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40466, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40467 q = 1) (hb : d322255 q = 1) : d322522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40467, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40467, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40468 q = 1) (hb : d322255 q = 1) : d322523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40468, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40468, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40469 q = 1) (hb : d322255 q = 1) : d322524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40469, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40469, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290091 q = 1) (hb : d322255 q = 1) : d324092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290091, d324092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290091, d324092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98097 (p : Pattern) (ha : d290102 p = 1) (hb : d322255 p = 1) : d324103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290097 q = 1) (hb : d322255 q = 1) : d324098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290097, d324098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97551 q ha hb
    | true =>
      simp only [d290097, d324098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97521 q ha hb
  have h2 (q : Pattern) (ha : d290098 q = 1) (hb : d322255 q = 1) : d324099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290098, d324099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290098, d324099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290099 q = 1) (hb : d322255 q = 1) : d324100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290099, d324100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290099, d324100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290100 q = 1) (hb : d322255 q = 1) : d324101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290100, d324101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290100, d324101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290101 q = 1) (hb : d322255 q = 1) : d324102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290101, d324102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290101, d324102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290102 q = 1) (hb : d322255 q = 1) : d324103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290102, d324103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290102, d324103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98098 (p : Pattern) (ha : d290108 p = 1) (hb : d322255 p = 1) : d324109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40471 q = 1) (hb : d322255 q = 1) : d322526 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40471, d322526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97513 q ha hb
    | true =>
      simp only [d40471, d322526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97516 q ha hb
  have h2 (q : Pattern) (ha : d40472 q = 1) (hb : d322255 q = 1) : d322527 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40472, d322527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40472, d322527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290089 q = 1) (hb : d322255 q = 1) : d324090 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290089, d324090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290089, d324090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290090 q = 1) (hb : d322255 q = 1) : d324091 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290090, d324091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290090, d324091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290092 q = 1) (hb : d322255 q = 1) : d324093 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290092, d324093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290092, d324093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98096 q ha hb
  have h6 (q : Pattern) (ha : d290093 q = 1) (hb : d322255 q = 1) : d324094 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290093, d324094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290093, d324094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d290094 q = 1) (hb : d322255 q = 1) : d324095 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290094, d324095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290094, d324095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d290095 q = 1) (hb : d322255 q = 1) : d324096 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290095, d324096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290095, d324096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d290096 q = 1) (hb : d322255 q = 1) : d324097 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290096, d324097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290096, d324097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290103 q = 1) (hb : d322255 q = 1) : d324104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290103, d324104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290103, d324104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98097 q ha hb
  have h11 (q : Pattern) (ha : d290104 q = 1) (hb : d322255 q = 1) : d324105 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290104, d324105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290104, d324105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d290105 q = 1) (hb : d322255 q = 1) : d324106 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290105, d324106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290105, d324106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d290106 q = 1) (hb : d322255 q = 1) : d324107 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290106, d324107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290106, d324107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d290107 q = 1) (hb : d322255 q = 1) : d324108 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290107, d324108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290107, d324108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d290108 q = 1) (hb : d322255 q = 1) : d324109 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290108, d324109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290108, d324109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98099 (p : Pattern) (ha : d290114 p = 1) (hb : d322255 p = 1) : d324115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290109 q = 1) (hb : d322255 q = 1) : d324110 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290109, d324110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290109, d324110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98098 q ha hb
  have h2 (q : Pattern) (ha : d290110 q = 1) (hb : d322255 q = 1) : d324111 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290110, d324111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290110, d324111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290111 q = 1) (hb : d322255 q = 1) : d324112 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290111, d324112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290111, d324112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290112 q = 1) (hb : d322255 q = 1) : d324113 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290112, d324113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290112, d324113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290113 q = 1) (hb : d322255 q = 1) : d324114 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290113, d324114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290113, d324114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290114 q = 1) (hb : d322255 q = 1) : d324115 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290114, d324115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290114, d324115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98100 (p : Pattern) (ha : d290118 p = 1) (hb : d322255 p = 1) : d324119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40804 q = 1) (hb : d322255 q = 1) : d322777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40804, d322777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97565 q ha hb
    | true =>
      simp only [d40804, d322777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97566 q ha hb
  have h2 (q : Pattern) (ha : d40805 q = 1) (hb : d322255 q = 1) : d322778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40805, d322778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40805, d322778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40806 q = 1) (hb : d322255 q = 1) : d322779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40806, d322779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40806, d322779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40807 q = 1) (hb : d322255 q = 1) : d322780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40807, d322780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40807, d322780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40808 q = 1) (hb : d322255 q = 1) : d322781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40808, d322781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40808, d322781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290118 q = 1) (hb : d322255 q = 1) : d324119 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290118, d324119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290118, d324119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98101 (p : Pattern) (ha : d290129 p = 1) (hb : d322255 p = 1) : d324130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290124 q = 1) (hb : d322255 q = 1) : d324125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290124, d324125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97606 q ha hb
    | true =>
      simp only [d290124, d324125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97574 q ha hb
  have h2 (q : Pattern) (ha : d290125 q = 1) (hb : d322255 q = 1) : d324126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290125, d324126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290125, d324126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290126 q = 1) (hb : d322255 q = 1) : d324127 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290126, d324127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290126, d324127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290127 q = 1) (hb : d322255 q = 1) : d324128 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290127, d324128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290127, d324128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290128 q = 1) (hb : d322255 q = 1) : d324129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290128, d324129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290128, d324129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290129 q = 1) (hb : d322255 q = 1) : d324130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290129, d324130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290129, d324130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98102 (p : Pattern) (ha : d290135 p = 1) (hb : d322255 p = 1) : d324136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40810 q = 1) (hb : d322255 q = 1) : d322783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40810, d322783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97564 q ha hb
    | true =>
      simp only [d40810, d322783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97567 q ha hb
  have h2 (q : Pattern) (ha : d40811 q = 1) (hb : d322255 q = 1) : d322784 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40811, d322784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40811, d322784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290116 q = 1) (hb : d322255 q = 1) : d324117 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290116, d324117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290116, d324117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290117 q = 1) (hb : d322255 q = 1) : d324118 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290117, d324118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290117, d324118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290119 q = 1) (hb : d322255 q = 1) : d324120 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290119, d324120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290119, d324120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98100 q ha hb
  have h6 (q : Pattern) (ha : d290120 q = 1) (hb : d322255 q = 1) : d324121 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290120, d324121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290120, d324121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d290121 q = 1) (hb : d322255 q = 1) : d324122 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290121, d324122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290121, d324122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d290122 q = 1) (hb : d322255 q = 1) : d324123 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290122, d324123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290122, d324123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d290123 q = 1) (hb : d322255 q = 1) : d324124 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290123, d324124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290123, d324124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290130 q = 1) (hb : d322255 q = 1) : d324131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290130, d324131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290130, d324131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98101 q ha hb
  have h11 (q : Pattern) (ha : d290131 q = 1) (hb : d322255 q = 1) : d324132 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290131, d324132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290131, d324132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d290132 q = 1) (hb : d322255 q = 1) : d324133 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290132, d324133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290132, d324133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d290133 q = 1) (hb : d322255 q = 1) : d324134 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290133, d324134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290133, d324134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d290134 q = 1) (hb : d322255 q = 1) : d324135 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290134, d324135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290134, d324135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d290135 q = 1) (hb : d322255 q = 1) : d324136 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290135, d324136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290135, d324136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98103 (p : Pattern) (ha : d290141 p = 1) (hb : d322255 p = 1) : d324142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290136 q = 1) (hb : d322255 q = 1) : d324137 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290136, d324137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290136, d324137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98102 q ha hb
  have h2 (q : Pattern) (ha : d290137 q = 1) (hb : d322255 q = 1) : d324138 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290137, d324138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290137, d324138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290138 q = 1) (hb : d322255 q = 1) : d324139 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290138, d324139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290138, d324139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290139 q = 1) (hb : d322255 q = 1) : d324140 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290139, d324140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290139, d324140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290140 q = 1) (hb : d322255 q = 1) : d324141 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290140, d324141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290140, d324141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290141 q = 1) (hb : d322255 q = 1) : d324142 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290141, d324142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290141, d324142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98104 (p : Pattern) (ha : d322255 p = 1) (hb : d333402 p = 1) : d324206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39765 q = 1) (hb : d322255 q = 1) : d323776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39765, d323776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97420 q ha hb
    | true =>
      simp only [d39765, d323776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97421 q ha hb
  have h2 (q : Pattern) (ha : d39766 q = 1) (hb : d322255 q = 1) : d323777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39766, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39766, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39767 q = 1) (hb : d322255 q = 1) : d323778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39767, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39767, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39768 q = 1) (hb : d322255 q = 1) : d323779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39768, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39768, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39769 q = 1) (hb : d322255 q = 1) : d323780 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39769, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39769, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d333402 q = 1) : d324206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333402, d324206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333402, d324206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro98105 (p : Pattern) (ha : d322255 p = 1) (hb : d333413 p = 1) : d324217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d333408 q = 1) : d324212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333408, d324212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97461 q hb ha
    | true =>
      simp only [d333408, d324212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97429 q hb ha
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d333409 q = 1) : d324213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333409, d324213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333409, d324213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d333410 q = 1) : d324214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333410, d324214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333410, d324214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d333411 q = 1) : d324215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333411, d324215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333411, d324215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d333412 q = 1) : d324216 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333412, d324216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333412, d324216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d333413 q = 1) : d324217 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333413, d324217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333413, d324217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98106 (p : Pattern) (ha : d322255 p = 1) (hb : d333419 p = 1) : d324223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39771 q = 1) (hb : d322255 q = 1) : d323782 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39771, d323782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97419 q ha hb
    | true =>
      simp only [d39771, d323782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97422 q ha hb
  have h2 (q : Pattern) (ha : d39772 q = 1) (hb : d322255 q = 1) : d323783 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39772, d323783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39772, d323783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d333400 q = 1) : d324204 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333400, d324204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d333400, d324204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d333401 q = 1) : d324205 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333401, d324205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333401, d324205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d333403 q = 1) : d324207 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333403, d324207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333403, d324207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98104 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d333404 q = 1) : d324208 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333404, d324208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333404, d324208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d322255 q = 1) (hb : d333405 q = 1) : d324209 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333405, d324209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333405, d324209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d322255 q = 1) (hb : d333406 q = 1) : d324210 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333406, d324210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d333406, d324210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d322255 q = 1) (hb : d333407 q = 1) : d324211 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333407, d324211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333407, d324211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322255 q = 1) (hb : d333414 q = 1) : d324218 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333414, d324218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333414, d324218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98105 q ha hb
  have h11 (q : Pattern) (ha : d322255 q = 1) (hb : d333415 q = 1) : d324219 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333415, d324219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333415, d324219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d322255 q = 1) (hb : d333416 q = 1) : d324220 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333416, d324220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d333416, d324220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d322255 q = 1) (hb : d333417 q = 1) : d324221 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333417, d324221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d333417, d324221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d322255 q = 1) (hb : d333418 q = 1) : d324222 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333418, d324222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d333418, d324222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d322255 q = 1) (hb : d333419 q = 1) : d324223 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333419, d324223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d333419, d324223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98107 (p : Pattern) (ha : d322255 p = 1) (hb : d333425 p = 1) : d324229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d333420 q = 1) : d324224 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333420, d324224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333420, d324224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98106 q ha hb
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d333421 q = 1) : d324225 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333421, d324225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333421, d324225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d333422 q = 1) : d324226 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333422, d324226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333422, d324226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d333423 q = 1) : d324227 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333423, d324227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333423, d324227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d333424 q = 1) : d324228 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333424, d324228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333424, d324228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d333425 q = 1) : d324229 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333425, d324229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333425, d324229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98108 (p : Pattern) (ha : d322255 p = 1) (hb : d338550 p = 1) : d324147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41239 q = 1) (hb : d322255 q = 1) : d323090 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d41239, d323090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97624 q ha hb
    | true =>
      simp only [d41239, d323090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97625 q ha hb
  have h2 (q : Pattern) (ha : d41240 q = 1) (hb : d322255 q = 1) : d323091 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d41240, d323091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41240, d323091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d41241 q = 1) (hb : d322255 q = 1) : d323092 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d41241, d323092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41241, d323092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d41242 q = 1) (hb : d322255 q = 1) : d323093 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d41242, d323093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41242, d323093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d41243 q = 1) (hb : d322255 q = 1) : d323094 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d41243, d323094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41243, d323094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338550 q = 1) : d324147 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338550, d324147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338550, d324147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro98109 (p : Pattern) (ha : d322255 p = 1) (hb : d338561 p = 1) : d324158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d338556 q = 1) : d324153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d338556, d324153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97664 q hb ha
    | true =>
      simp only [d338556, d324153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97633 q hb ha
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d338557 q = 1) : d324154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d338557, d324154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338557, d324154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338558 q = 1) : d324155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d338558, d324155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338558, d324155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338559 q = 1) : d324156 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d338559, d324156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338559, d324156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338560 q = 1) : d324157 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d338560, d324157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338560, d324157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338561 q = 1) : d324158 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338561, d324158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338561, d324158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98110 (p : Pattern) (ha : d322255 p = 1) (hb : d338567 p = 1) : d324164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41245 q = 1) (hb : d322255 q = 1) : d323096 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d41245, d323096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97623 q ha hb
    | true =>
      simp only [d41245, d323096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97626 q ha hb
  have h2 (q : Pattern) (ha : d41246 q = 1) (hb : d322255 q = 1) : d323097 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d41246, d323097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41246, d323097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338548 q = 1) : d324145 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338548, d324145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d338548, d324145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338549 q = 1) : d324146 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338549, d324146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338549, d324146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338551 q = 1) : d324148 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338551, d324148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338551, d324148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98108 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338552 q = 1) : d324149 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338552, d324149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338552, d324149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d322255 q = 1) (hb : d338553 q = 1) : d324150 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338553, d324150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d338553, d324150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d322255 q = 1) (hb : d338554 q = 1) : d324151 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338554, d324151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d338554, d324151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d322255 q = 1) (hb : d338555 q = 1) : d324152 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338555, d324152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338555, d324152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322255 q = 1) (hb : d338562 q = 1) : d324159 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338562, d324159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338562, d324159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98109 q ha hb
  have h11 (q : Pattern) (ha : d322255 q = 1) (hb : d338563 q = 1) : d324160 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338563, d324160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d338563, d324160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d322255 q = 1) (hb : d338564 q = 1) : d324161 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338564, d324161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d338564, d324161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d322255 q = 1) (hb : d338565 q = 1) : d324162 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338565, d324162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d338565, d324162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d322255 q = 1) (hb : d338566 q = 1) : d324163 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338566, d324163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d338566, d324163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d322255 q = 1) (hb : d338567 q = 1) : d324164 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d338567, d324164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d338567, d324164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98111 (p : Pattern) (ha : d322255 p = 1) (hb : d338573 p = 1) : d324170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d338568 q = 1) : d324165 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d338568, d324165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338568, d324165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98110 q ha hb
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d338569 q = 1) : d324166 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d338569, d324166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338569, d324166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338570 q = 1) : d324167 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d338570, d324167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338570, d324167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338571 q = 1) : d324168 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d338571, d324168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338571, d324168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338572 q = 1) : d324169 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d338572, d324169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338572, d324169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338573 q = 1) : d324170 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d338573, d324170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338573, d324170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98112 (p : Pattern) (ha : d322255 p = 1) (hb : d338579 p = 1) : d324176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41766 q = 1) (hb : d322255 q = 1) : d323442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d41766, d323442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97688 q ha hb
    | true =>
      simp only [d41766, d323442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97689 q ha hb
  have h2 (q : Pattern) (ha : d41767 q = 1) (hb : d322255 q = 1) : d323443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d41767, d323443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41767, d323443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d41768 q = 1) (hb : d322255 q = 1) : d323444 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d41768, d323444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41768, d323444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d41769 q = 1) (hb : d322255 q = 1) : d323445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d41769, d323445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41769, d323445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d41770 q = 1) (hb : d322255 q = 1) : d323446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d41770, d323446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41770, d323446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338579 q = 1) : d324176 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338579, d324176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338579, d324176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro98113 (p : Pattern) (ha : d322255 p = 1) (hb : d338590 p = 1) : d324187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d338585 q = 1) : d324182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d338585, d324182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97730 q hb ha
    | true =>
      simp only [d338585, d324182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97697 q hb ha
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d338586 q = 1) : d324183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d338586, d324183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338586, d324183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338587 q = 1) : d324184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d338587, d324184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338587, d324184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338588 q = 1) : d324185 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d338588, d324185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338588, d324185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338589 q = 1) : d324186 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d338589, d324186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338589, d324186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338590 q = 1) : d324187 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338590, d324187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338590, d324187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98114 (p : Pattern) (ha : d322255 p = 1) (hb : d338596 p = 1) : d324193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41772 q = 1) (hb : d322255 q = 1) : d323448 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d41772, d323448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97687 q ha hb
    | true =>
      simp only [d41772, d323448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97690 q ha hb
  have h2 (q : Pattern) (ha : d41773 q = 1) (hb : d322255 q = 1) : d323449 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d41773, d323449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41773, d323449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338577 q = 1) : d324174 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338577, d324174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d338577, d324174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338578 q = 1) : d324175 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338578, d324175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338578, d324175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338580 q = 1) : d324177 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338580, d324177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338580, d324177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98112 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338581 q = 1) : d324178 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338581, d324178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338581, d324178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d322255 q = 1) (hb : d338582 q = 1) : d324179 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338582, d324179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d338582, d324179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d322255 q = 1) (hb : d338583 q = 1) : d324180 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338583, d324180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d338583, d324180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d322255 q = 1) (hb : d338584 q = 1) : d324181 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338584, d324181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338584, d324181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322255 q = 1) (hb : d338591 q = 1) : d324188 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338591, d324188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338591, d324188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98113 q ha hb
  have h11 (q : Pattern) (ha : d322255 q = 1) (hb : d338592 q = 1) : d324189 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338592, d324189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d338592, d324189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d322255 q = 1) (hb : d338593 q = 1) : d324190 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338593, d324190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d338593, d324190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d322255 q = 1) (hb : d338594 q = 1) : d324191 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338594, d324191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d338594, d324191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d322255 q = 1) (hb : d338595 q = 1) : d324192 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338595, d324192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d338595, d324192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d322255 q = 1) (hb : d338596 q = 1) : d324193 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d338596, d324193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d338596, d324193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98115 (p : Pattern) (ha : d322255 p = 1) (hb : d338602 p = 1) : d324199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d338597 q = 1) : d324194 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d338597, d324194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338597, d324194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98114 q ha hb
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d338598 q = 1) : d324195 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d338598, d324195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338598, d324195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338599 q = 1) : d324196 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d338599, d324196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338599, d324196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338600 q = 1) : d324197 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d338600, d324197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338600, d324197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338601 q = 1) : d324198 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d338601, d324198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338601, d324198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338602 q = 1) : d324199 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d338602, d324199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338602, d324199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98116 (p : Pattern) (ha : d322255 p = 1) (hb : d338608 p = 1) : d324235 p = 1 := by
  have h0 (q : Pattern) (ha : d290115 q = 1) (hb : d322255 q = 1) : d324116 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290115, d324116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98095 q ha hb
    | true =>
      simp only [d290115, d324116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98099 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d290142 q = 1) (hb : d322255 q = 1) : d324143 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290142, d324143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290142, d324143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98103 q ha hb
  have h3 (q : Pattern) (ha : d290143 q = 1) (hb : d322255 q = 1) : d324144 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290143, d324144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290143, d324144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338574 q = 1) : d324171 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d338574, d324171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338574, d324171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98111 q ha hb
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338575 q = 1) : d324172 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d338575, d324172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338575, d324172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338576 q = 1) : d324173 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d338576, d324173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d338576, d324173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322255 q = 1) (hb : d338603 q = 1) : d324200 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d338603, d324200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338603, d324200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98115 q ha hb
  have h8 (q : Pattern) (ha : d322255 q = 1) (hb : d338604 q = 1) : d324201 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d338604, d324201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338604, d324201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d322255 q = 1) (hb : d338605 q = 1) : d324202 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d338605, d324202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338605, d324202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322255 q = 1) (hb : d338606 q = 1) : d324203 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d338606, d324203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d338606, d324203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d322255 q = 1) (hb : d333426 q = 1) : d324230 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333426, d324230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333426, d324230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98107 q ha hb
  have h12 (q : Pattern) (ha : d322255 q = 1) (hb : d333427 q = 1) : d324231 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333427, d324231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333427, d324231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d322255 q = 1) (hb : d333428 q = 1) : d324232 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333428, d324232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333428, d324232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d322255 q = 1) (hb : d333429 q = 1) : d324233 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d333429, d324233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333429, d324233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d322255 q = 1) (hb : d338607 q = 1) : d324234 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d338607, d324234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d338607, d324234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d322255 q = 1) (hb : d338608 q = 1) : d324235 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d338608, d324235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d338608, d324235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro98117 (p : Pattern) (ha : d322255 p = 1) (hb : d338614 p = 1) : d324241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d338609 q = 1) : d324236 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d338609, d324236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98116 q ha hb
    | true =>
      simp only [d338609, d324236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d338610 q = 1) : d324237 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d338610, d324237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338610, d324237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338611 q = 1) : d324238 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d338611, d324238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338611, d324238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338612 q = 1) : d324239 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d338612, d324239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338612, d324239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338613 q = 1) : d324240 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d338613, d324240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338613, d324240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338614 q = 1) : d324241 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d338614, d324241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338614, d324241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98118 (p : Pattern) (ha : d322255 p = 1) (hb : d338620 p = 1) : d324247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d338615 q = 1) : d324242 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d338615, d324242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98117 q ha hb
    | true =>
      simp only [d338615, d324242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d338616 q = 1) : d324243 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d338616, d324243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338616, d324243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338617 q = 1) : d324244 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d338617, d324244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338617, d324244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338618 q = 1) : d324245 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d338618, d324245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338618, d324245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338619 q = 1) : d324246 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d338619, d324246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338619, d324246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338620 q = 1) : d324247 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d338620, d324247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338620, d324247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98119 (p : Pattern) (ha : d322255 p = 1) (hb : d338626 p = 1) : d324253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d338621 q = 1) : d324248 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d338621, d324248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98118 q ha hb
    | true =>
      simp only [d338621, d324248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d338622 q = 1) : d324249 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d338622, d324249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338622, d324249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338623 q = 1) : d324250 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d338623, d324250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338623, d324250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338624 q = 1) : d324251 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d338624, d324251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338624, d324251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338625 q = 1) : d324252 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d338625, d324252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338625, d324252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338626 q = 1) : d324253 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d338626, d324253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338626, d324253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98120 (p : Pattern) (ha : d322255 p = 1) (hb : d338632 p = 1) : d324259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d338627 q = 1) : d324254 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d338627, d324254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98119 q ha hb
    | true =>
      simp only [d338627, d324254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d338628 q = 1) : d324255 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d338628, d324255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338628, d324255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338629 q = 1) : d324256 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d338629, d324256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338629, d324256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338630 q = 1) : d324257 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d338630, d324257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338630, d324257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338631 q = 1) : d324258 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d338631, d324258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338631, d324258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338632 q = 1) : d324259 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d338632, d324259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338632, d324259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98121 (p : Pattern) (ha : d322255 p = 1) (hb : d338638 p = 1) : d324265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d338633 q = 1) : d324260 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d338633, d324260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98120 q ha hb
    | true =>
      simp only [d338633, d324260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d338634 q = 1) : d324261 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d338634, d324261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338634, d324261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338635 q = 1) : d324262 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d338635, d324262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338635, d324262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338636 q = 1) : d324263 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d338636, d324263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338636, d324263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338637 q = 1) : d324264 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d338637, d324264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338637, d324264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338638 q = 1) : d324265 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d338638, d324265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338638, d324265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98122 (p : Pattern) (ha : d322255 p = 1) (hb : d338644 p = 1) : d324271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d338639 q = 1) : d324266 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d338639, d324266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98121 q ha hb
    | true =>
      simp only [d338639, d324266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d338640 q = 1) : d324267 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d338640, d324267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338640, d324267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338641 q = 1) : d324268 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d338641, d324268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338641, d324268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338642 q = 1) : d324269 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d338642, d324269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338642, d324269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338643 q = 1) : d324270 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d338643, d324270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338643, d324270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338644 q = 1) : d324271 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d338644, d324271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338644, d324271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98123 (p : Pattern) (ha : d322255 p = 1) (hb : d338650 p = 1) : d324277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322255 q = 1) (hb : d338645 q = 1) : d324272 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d338645, d324272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98122 q ha hb
    | true =>
      simp only [d338645, d324272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d322255 q = 1) (hb : d338646 q = 1) : d324273 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d338646, d324273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338646, d324273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d322255 q = 1) (hb : d338647 q = 1) : d324274 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d338647, d324274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338647, d324274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d322255 q = 1) (hb : d338648 q = 1) : d324275 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d338648, d324275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338648, d324275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d322255 q = 1) (hb : d338649 q = 1) : d324276 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d338649, d324276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338649, d324276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d322255 q = 1) (hb : d338650 q = 1) : d324277 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d338650, d324277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338650, d324277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98124 (p : Pattern) (ha : d262145 p = 1) (hb : d322345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262099 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262134 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262013 q = 1) (hb : d322281 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262013, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97750 q ha hb
    | true =>
      simp only [d262013, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d262135 q = 1) (hb : d322341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262135, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262135, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262141 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262142 q = 1) (hb : d322342 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262142, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262142, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262143 q = 1) (hb : d322343 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262143, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262143, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262144 q = 1) (hb : d322344 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262144, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262144, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262145 q = 1) (hb : d322345 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262145, d322345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262145, d322345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98125 (p : Pattern) (ha : d262164 p = 1) (hb : d322352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262134 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262013 q = 1) (hb : d322281 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262013, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97750 q ha hb
    | true =>
      simp only [d262013, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d262135 q = 1) (hb : d322341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262135, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262135, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262141 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262142 q = 1) (hb : d322342 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262142, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262142, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262143 q = 1) (hb : d322343 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262143, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262143, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262144 q = 1) (hb : d322344 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262144, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262144, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262150 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262154 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262156 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262020 q = 1) (hb : d322288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262020, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97752 q ha hb
    | true =>
      simp only [d262020, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d262157 q = 1) (hb : d322348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262157, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262157, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262160 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262161 q = 1) (hb : d322349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262161, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262161, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262162 q = 1) (hb : d322350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262162, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262162, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262163 q = 1) (hb : d322351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262163, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262163, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262164 q = 1) (hb : d322352 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262164, d322352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262164, d322352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98126 (p : Pattern) (ha : d262173 p = 1) (hb : d324067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262156 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262020 q = 1) (hb : d322288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262020, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97752 q ha hb
    | true =>
      simp only [d262020, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d262157 q = 1) (hb : d322348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262157, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262157, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262160 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262161 q = 1) (hb : d322349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262161, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262161, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262171 q = 1) (hb : d322350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262171, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262171, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262172 q = 1) (hb : d322351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262172, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262172, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262173 q = 1) (hb : d324067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262173, d324067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262173, d324067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98127 (p : Pattern) (ha : d262213 p = 1) (hb : d324077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262202 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262056 q = 1) (hb : d322324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262056, d322324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97757 q ha hb
    | true =>
      simp only [d262056, d322324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d262203 q = 1) (hb : d324073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262203, d324073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262203, d324073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262209 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262210 q = 1) (hb : d324074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262210, d324074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262210, d324074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262211 q = 1) (hb : d324075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262211, d324075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262211, d324075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262212 q = 1) (hb : d324076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262212, d324076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262212, d324076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262213 q = 1) (hb : d324077 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262213, d324077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262213, d324077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98128 (p : Pattern) (ha : d262219 p = 1) (hb : d324083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262087 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262165 q = 1) (hb : d322353 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262165, d322353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98124 q ha hb
    | true =>
      simp only [d262165, d322353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98125 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262167 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262168 q = 1) (hb : d322354 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262168, d322354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262168, d322354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262169 q = 1) (hb : d324065 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262169, d324065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262169, d324065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262170 q = 1) (hb : d324066 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262170, d324066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262170, d324066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262174 q = 1) (hb : d324068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262174, d324068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262174, d324068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98126 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262175 q = 1) (hb : d324069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262175, d324069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262175, d324069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262176 q = 1) (hb : d324070 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262176, d324070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262176, d324070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262177 q = 1) (hb : d324071 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262177, d324071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262177, d324071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262178 q = 1) (hb : d324072 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262178, d324072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262178, d324072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262214 q = 1) (hb : d324078 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262214, d324078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262214, d324078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98127 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262215 q = 1) (hb : d324079 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262215, d324079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262215, d324079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262216 q = 1) (hb : d324080 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262216, d324080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262216, d324080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262217 q = 1) (hb : d324081 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262217, d324081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262217, d324081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262218 q = 1) (hb : d324082 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262218, d324082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262218, d324082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262219 q = 1) (hb : d324083 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262219, d324083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262219, d324083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98129 (p : Pattern) (ha : d262225 p = 1) (hb : d324089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d262068 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d262068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d262068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66694 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d262069 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d262069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d262069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d262070 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d262070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d262070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d262071 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d262071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d262071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d262072 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d262072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d262072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262220 q = 1) (hb : d324084 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262220, d324084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262220, d324084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98128 q ha hb
  have h8 (q : Pattern) (ha : d262221 q = 1) (hb : d324085 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262221, d324085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262221, d324085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262222 q = 1) (hb : d324086 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262222, d324086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262222, d324086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262223 q = 1) (hb : d324087 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262223, d324087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262223, d324087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d262224 q = 1) (hb : d324088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262224, d324088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262224, d324088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d262225 q = 1) (hb : d324089 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262225, d324089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d262225, d324089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro98130 (p : Pattern) (ha : d262339 p = 1) (hb : d322515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262278 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262328 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262243 q = 1) (hb : d322510 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262243, d322510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97788 q ha hb
    | true =>
      simp only [d262243, d322510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97789 q ha hb
  have h5 (q : Pattern) (ha : d262329 q = 1) (hb : d322511 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262329, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262329, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262335 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262336 q = 1) (hb : d322512 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262336, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262336, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262337 q = 1) (hb : d322513 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262337, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262337, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262338 q = 1) (hb : d322514 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262338, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262338, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262339 q = 1) (hb : d322515 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262339, d322515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262339, d322515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98131 (p : Pattern) (ha : d262360 p = 1) (hb : d322525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262278 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262243 q = 1) (hb : d322510 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262243, d322510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97788 q ha hb
    | true =>
      simp only [d262243, d322510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97789 q ha hb
  have h4 (q : Pattern) (ha : d262329 q = 1) (hb : d322511 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262329, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262329, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262335 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262336 q = 1) (hb : d322512 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262336, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262336, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262337 q = 1) (hb : d322513 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262337, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262337, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262338 q = 1) (hb : d322514 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262338, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262338, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262345 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262350 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262352 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262253 q = 1) (hb : d322520 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262253, d322520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97791 q ha hb
    | true =>
      simp only [d262253, d322520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97792 q ha hb
  have h13 (q : Pattern) (ha : d262353 q = 1) (hb : d322521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262353, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262353, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262356 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262357 q = 1) (hb : d322522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262357, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262357, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262358 q = 1) (hb : d322523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262358, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262358, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262359 q = 1) (hb : d322524 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262359, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262359, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262360 q = 1) (hb : d322525 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262360, d322525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262360, d322525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98132 (p : Pattern) (ha : d262380 p = 1) (hb : d324092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262352 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262253 q = 1) (hb : d322520 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262253, d322520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97791 q ha hb
    | true =>
      simp only [d262253, d322520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97792 q ha hb
  have h3 (q : Pattern) (ha : d262353 q = 1) (hb : d322521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262353, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262353, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262356 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262357 q = 1) (hb : d322522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262357, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262357, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262378 q = 1) (hb : d322523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262378, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262378, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262379 q = 1) (hb : d322524 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262379, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262379, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262380 q = 1) (hb : d324092 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262380, d324092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262380, d324092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98133 (p : Pattern) (ha : d262448 p = 1) (hb : d324103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262437 q = 1) (hb : d324098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262437, d324098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97826 q ha hb
    | true =>
      simp only [d262437, d324098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97829 q ha hb
  have h3 (q : Pattern) (ha : d262438 q = 1) (hb : d324099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262438, d324099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262438, d324099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262444 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262445 q = 1) (hb : d324100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262445, d324100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262445, d324100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262446 q = 1) (hb : d324101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262446, d324101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262446, d324101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262447 q = 1) (hb : d324102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262447, d324102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262447, d324102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262448 q = 1) (hb : d324103 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262448, d324103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262448, d324103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98134 (p : Pattern) (ha : d262461 p = 1) (hb : d324109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262261 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262361 q = 1) (hb : d322526 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262361, d322526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98130 q ha hb
    | true =>
      simp only [d262361, d322526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98131 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262374 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262375 q = 1) (hb : d322527 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262375, d322527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262375, d322527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262376 q = 1) (hb : d324090 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262376, d324090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262376, d324090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262377 q = 1) (hb : d324091 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262377, d324091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262377, d324091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262381 q = 1) (hb : d324093 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262381, d324093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262381, d324093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98132 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d262383 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262384 q = 1) (hb : d324094 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262384, d324094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262384, d324094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262385 q = 1) (hb : d324095 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262385, d324095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262385, d324095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262386 q = 1) (hb : d324096 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262386, d324096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262386, d324096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262387 q = 1) (hb : d324097 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262387, d324097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262387, d324097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262449 q = 1) (hb : d324104 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262449, d324104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262449, d324104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98133 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262456 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262457 q = 1) (hb : d324105 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262457, d324105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262457, d324105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262458 q = 1) (hb : d324106 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262458, d324106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262458, d324106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262459 q = 1) (hb : d324107 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262459, d324107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262459, d324107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262460 q = 1) (hb : d324108 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262460, d324108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262460, d324108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262461 q = 1) (hb : d324109 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262461, d324109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262461, d324109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98135 (p : Pattern) (ha : d262467 p = 1) (hb : d324115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262462 q = 1) (hb : d324110 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262462, d324110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262462, d324110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98134 q ha hb
  have h2 (q : Pattern) (ha : d262463 q = 1) (hb : d324111 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262463, d324111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262463, d324111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d262464 q = 1) (hb : d324112 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262464, d324112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262464, d324112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d262465 q = 1) (hb : d324113 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262465, d324113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262465, d324113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d262466 q = 1) (hb : d324114 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262466, d324114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262466, d324114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d262467 q = 1) (hb : d324115 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262467, d324115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262467, d324115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98136 (p : Pattern) (ha : d262607 p = 1) (hb : d322772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262530 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262596 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262504 q = 1) (hb : d322767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262504, d322767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97839 q ha hb
    | true =>
      simp only [d262504, d322767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97840 q ha hb
  have h5 (q : Pattern) (ha : d262597 q = 1) (hb : d322768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262597, d322768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262597, d322768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262603 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262604 q = 1) (hb : d322769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262604, d322769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262604, d322769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262605 q = 1) (hb : d322770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262605, d322770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262605, d322770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262606 q = 1) (hb : d322771 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262606, d322771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262606, d322771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262607 q = 1) (hb : d322772 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262607, d322772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262607, d322772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98137 (p : Pattern) (ha : d262628 p = 1) (hb : d322782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262530 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262504 q = 1) (hb : d322767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262504, d322767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97839 q ha hb
    | true =>
      simp only [d262504, d322767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97840 q ha hb
  have h4 (q : Pattern) (ha : d262597 q = 1) (hb : d322768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262597, d322768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262597, d322768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262603 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262604 q = 1) (hb : d322769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262604, d322769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262604, d322769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262605 q = 1) (hb : d322770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262605, d322770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262605, d322770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262606 q = 1) (hb : d322771 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262606, d322771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262606, d322771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262613 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262618 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262620 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262514 q = 1) (hb : d322777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262514, d322777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97842 q ha hb
    | true =>
      simp only [d262514, d322777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97843 q ha hb
  have h13 (q : Pattern) (ha : d262621 q = 1) (hb : d322778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262621, d322778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262621, d322778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262625 q = 1) (hb : d322779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262625, d322779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262625, d322779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262626 q = 1) (hb : d322780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262626, d322780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262626, d322780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262627 q = 1) (hb : d322781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262627, d322781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262627, d322781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262628 q = 1) (hb : d322782 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262628, d322782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262628, d322782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98138 (p : Pattern) (ha : d262648 p = 1) (hb : d324119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262514 q = 1) (hb : d322777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262514, d322777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97842 q ha hb
    | true =>
      simp only [d262514, d322777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97843 q ha hb
  have h3 (q : Pattern) (ha : d262621 q = 1) (hb : d322778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262621, d322778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262621, d322778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262625 q = 1) (hb : d322779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262625, d322779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262625, d322779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262646 q = 1) (hb : d322780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262646, d322780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262646, d322780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262647 q = 1) (hb : d322781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262647, d322781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262647, d322781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262648 q = 1) (hb : d324119 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262648, d324119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262648, d324119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98139 (p : Pattern) (ha : d262733 p = 1) (hb : d324130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262722 q = 1) (hb : d324125 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262722, d324125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97881 q ha hb
    | true =>
      simp only [d262722, d324125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97884 q ha hb
  have h3 (q : Pattern) (ha : d262723 q = 1) (hb : d324126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262723, d324126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262723, d324126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262729 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262730 q = 1) (hb : d324127 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262730, d324127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262730, d324127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262731 q = 1) (hb : d324128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262731, d324128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262731, d324128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262732 q = 1) (hb : d324129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262732, d324129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262732, d324129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262733 q = 1) (hb : d324130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262733, d324130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262733, d324130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98140 (p : Pattern) (ha : d262746 p = 1) (hb : d324136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262522 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262629 q = 1) (hb : d322783 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262629, d322783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98136 q ha hb
    | true =>
      simp only [d262629, d322783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98137 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262643 q = 1) (hb : d322784 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262643, d322784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262643, d322784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262644 q = 1) (hb : d324117 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262644, d324117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262644, d324117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262645 q = 1) (hb : d324118 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262645, d324118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262645, d324118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262649 q = 1) (hb : d324120 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262649, d324120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262649, d324120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98138 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d262651 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262652 q = 1) (hb : d324121 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262652, d324121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262652, d324121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262653 q = 1) (hb : d324122 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262653, d324122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262653, d324122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262654 q = 1) (hb : d324123 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262654, d324123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262654, d324123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262655 q = 1) (hb : d324124 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262655, d324124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262655, d324124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262734 q = 1) (hb : d324131 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262734, d324131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262734, d324131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98139 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262741 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262742 q = 1) (hb : d324132 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262742, d324132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262742, d324132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262743 q = 1) (hb : d324133 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262743, d324133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262743, d324133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262744 q = 1) (hb : d324134 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262744, d324134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262744, d324134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262745 q = 1) (hb : d324135 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262745, d324135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262745, d324135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262746 q = 1) (hb : d324136 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262746, d324136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262746, d324136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98141 (p : Pattern) (ha : d262752 p = 1) (hb : d324142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262747 q = 1) (hb : d324137 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262747, d324137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262747, d324137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98140 q ha hb
  have h2 (q : Pattern) (ha : d262748 q = 1) (hb : d324138 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262748, d324138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262748, d324138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d262749 q = 1) (hb : d324139 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262749, d324139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262749, d324139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d262750 q = 1) (hb : d324140 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262750, d324140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262750, d324140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d262751 q = 1) (hb : d324141 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262751, d324141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262751, d324141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d262752 q = 1) (hb : d324142 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262752, d324142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262752, d324142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98142 (p : Pattern) (ha : d262965 p = 1) (hb : d323085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262945 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262846 q = 1) (hb : d323080 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262846, d323080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97899 q ha hb
    | true =>
      simp only [d262846, d323080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97900 q ha hb
  have h5 (q : Pattern) (ha : d262946 q = 1) (hb : d323081 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262946, d323081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262946, d323081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262961 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262962 q = 1) (hb : d323082 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262962, d323082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262962, d323082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262963 q = 1) (hb : d323083 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262963, d323083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262963, d323083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262964 q = 1) (hb : d323084 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262964, d323084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262964, d323084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262965 q = 1) (hb : d323085 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262965, d323085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262965, d323085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98143 (p : Pattern) (ha : d262986 p = 1) (hb : d323095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262846 q = 1) (hb : d323080 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262846, d323080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97899 q ha hb
    | true =>
      simp only [d262846, d323080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97900 q ha hb
  have h4 (q : Pattern) (ha : d262946 q = 1) (hb : d323081 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262946, d323081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262946, d323081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262961 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262962 q = 1) (hb : d323082 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262962, d323082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262962, d323082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262963 q = 1) (hb : d323083 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262963, d323083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262963, d323083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262964 q = 1) (hb : d323084 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262964, d323084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262964, d323084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262971 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262976 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262978 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262856 q = 1) (hb : d323090 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262856, d323090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97902 q ha hb
    | true =>
      simp only [d262856, d323090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97903 q ha hb
  have h13 (q : Pattern) (ha : d262979 q = 1) (hb : d323091 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262979, d323091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262979, d323091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262982 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262983 q = 1) (hb : d323092 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262983, d323092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262983, d323092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262984 q = 1) (hb : d323093 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262984, d323093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262984, d323093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262985 q = 1) (hb : d323094 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262985, d323094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262985, d323094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262986 q = 1) (hb : d323095 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262986, d323095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262986, d323095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98144 (p : Pattern) (ha : d263006 p = 1) (hb : d324147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262856 q = 1) (hb : d323090 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262856, d323090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97902 q ha hb
    | true =>
      simp only [d262856, d323090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97903 q ha hb
  have h3 (q : Pattern) (ha : d262979 q = 1) (hb : d323091 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262979, d323091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262979, d323091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262983 q = 1) (hb : d323092 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262983, d323092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262983, d323092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263004 q = 1) (hb : d323093 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263004, d323093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263004, d323093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263005 q = 1) (hb : d323094 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263005, d323094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263005, d323094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263006 q = 1) (hb : d324147 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263006, d324147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263006, d324147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98145 (p : Pattern) (ha : d263127 p = 1) (hb : d324158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263107 q = 1) (hb : d324153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263107, d324153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97942 q ha hb
    | true =>
      simp only [d263107, d324153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97947 q ha hb
  have h3 (q : Pattern) (ha : d263108 q = 1) (hb : d324154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263108, d324154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263108, d324154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263123 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263124 q = 1) (hb : d324155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263124, d324155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263124, d324155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263125 q = 1) (hb : d324156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263125, d324156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263125, d324156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263126 q = 1) (hb : d324157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263126, d324157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263126, d324157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263127 q = 1) (hb : d324158 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263127, d324158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263127, d324158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98146 (p : Pattern) (ha : d263140 p = 1) (hb : d324164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262987 q = 1) (hb : d323096 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262987, d323096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98142 q ha hb
    | true =>
      simp only [d262987, d323096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98143 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263000 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263001 q = 1) (hb : d323097 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263001, d323097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263001, d323097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263002 q = 1) (hb : d324145 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263002, d324145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263002, d324145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263003 q = 1) (hb : d324146 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263003, d324146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263003, d324146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263007 q = 1) (hb : d324148 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263007, d324148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263007, d324148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98144 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263009 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263010 q = 1) (hb : d324149 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263010, d324149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263010, d324149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263011 q = 1) (hb : d324150 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263011, d324150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263011, d324150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263012 q = 1) (hb : d324151 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263012, d324151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263012, d324151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263013 q = 1) (hb : d324152 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263013, d324152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263013, d324152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263128 q = 1) (hb : d324159 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263128, d324159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263128, d324159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98145 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263136 q = 1) (hb : d324160 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263136, d324160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263136, d324160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263137 q = 1) (hb : d324161 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263137, d324161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263137, d324161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263138 q = 1) (hb : d324162 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263138, d324162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263138, d324162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263139 q = 1) (hb : d324163 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263139, d324163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263139, d324163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263140 q = 1) (hb : d324164 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263140, d324164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263140, d324164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98147 (p : Pattern) (ha : d263146 p = 1) (hb : d324170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263141 q = 1) (hb : d324165 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263141, d324165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263141, d324165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98146 q ha hb
  have h2 (q : Pattern) (ha : d263142 q = 1) (hb : d324166 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263142, d324166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263142, d324166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263143 q = 1) (hb : d324167 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263143, d324167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263143, d324167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263144 q = 1) (hb : d324168 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263144, d324168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263144, d324168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263145 q = 1) (hb : d324169 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263145, d324169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263145, d324169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263146 q = 1) (hb : d324170 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263146, d324170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263146, d324170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98148 (p : Pattern) (ha : d263364 p = 1) (hb : d323437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263276 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d263331 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d263250 q = 1) (hb : d323432 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263250, d323432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97963 q ha hb
    | true =>
      simp only [d263250, d323432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97964 q ha hb
  have h5 (q : Pattern) (ha : d263332 q = 1) (hb : d323433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263332, d323433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263332, d323433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d263360 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d263361 q = 1) (hb : d323434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263361, d323434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263361, d323434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d263362 q = 1) (hb : d323435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263362, d323435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263362, d323435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263363 q = 1) (hb : d323436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263363, d323436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263363, d323436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263364 q = 1) (hb : d323437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263364, d323437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263364, d323437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98149 (p : Pattern) (ha : d263385 p = 1) (hb : d323447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263276 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263331 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263250 q = 1) (hb : d323432 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263250, d323432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97963 q ha hb
    | true =>
      simp only [d263250, d323432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97964 q ha hb
  have h4 (q : Pattern) (ha : d263332 q = 1) (hb : d323433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263332, d323433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263332, d323433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d263360 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d263361 q = 1) (hb : d323434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263361, d323434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263361, d323434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d263362 q = 1) (hb : d323435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263362, d323435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263362, d323435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263363 q = 1) (hb : d323436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263363, d323436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263363, d323436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263370 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d263375 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d263377 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d263260 q = 1) (hb : d323442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263260, d323442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97966 q ha hb
    | true =>
      simp only [d263260, d323442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97967 q ha hb
  have h13 (q : Pattern) (ha : d263378 q = 1) (hb : d323443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263378, d323443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d263378, d323443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263381 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263382 q = 1) (hb : d323444 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263382, d323444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263382, d323444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263383 q = 1) (hb : d323445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263383, d323445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d263383, d323445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263384 q = 1) (hb : d323446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263384, d323446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d263384, d323446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d263385 q = 1) (hb : d323447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263385, d323447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263385, d323447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98150 (p : Pattern) (ha : d263405 p = 1) (hb : d324176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263260 q = 1) (hb : d323442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263260, d323442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97966 q ha hb
    | true =>
      simp only [d263260, d323442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97967 q ha hb
  have h3 (q : Pattern) (ha : d263378 q = 1) (hb : d323443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263378, d323443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263378, d323443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263382 q = 1) (hb : d323444 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263382, d323444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263382, d323444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263403 q = 1) (hb : d323445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263403, d323445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263403, d323445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263404 q = 1) (hb : d323446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263404, d323446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263404, d323446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263405 q = 1) (hb : d324176 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263405, d324176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263405, d324176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98151 (p : Pattern) (ha : d263537 p = 1) (hb : d324187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263506 q = 1) (hb : d324182 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263506, d324182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98007 q ha hb
    | true =>
      simp only [d263506, d324182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98013 q ha hb
  have h3 (q : Pattern) (ha : d263507 q = 1) (hb : d324183 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263507, d324183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263507, d324183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263533 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263534 q = 1) (hb : d324184 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263534, d324184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263534, d324184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263535 q = 1) (hb : d324185 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263535, d324185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263535, d324185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263536 q = 1) (hb : d324186 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263536, d324186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263536, d324186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263537 q = 1) (hb : d324187 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263537, d324187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263537, d324187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98152 (p : Pattern) (ha : d263550 p = 1) (hb : d324193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263268 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263386 q = 1) (hb : d323448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263386, d323448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98148 q ha hb
    | true =>
      simp only [d263386, d323448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98149 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263399 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263400 q = 1) (hb : d323449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263400, d323449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263400, d323449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263401 q = 1) (hb : d324174 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263401, d324174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263401, d324174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263402 q = 1) (hb : d324175 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263402, d324175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263402, d324175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263406 q = 1) (hb : d324177 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263406, d324177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263406, d324177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98150 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263408 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263409 q = 1) (hb : d324178 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263409, d324178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263409, d324178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263410 q = 1) (hb : d324179 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263410, d324179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263410, d324179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263411 q = 1) (hb : d324180 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263411, d324180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263411, d324180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263412 q = 1) (hb : d324181 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263412, d324181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263412, d324181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263538 q = 1) (hb : d324188 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263538, d324188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263538, d324188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98151 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263545 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263546 q = 1) (hb : d324189 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263546, d324189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263546, d324189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263547 q = 1) (hb : d324190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263547, d324190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263547, d324190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263548 q = 1) (hb : d324191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263548, d324191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263548, d324191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263549 q = 1) (hb : d324192 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263549, d324192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263549, d324192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263550 q = 1) (hb : d324193 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263550, d324193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263550, d324193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98153 (p : Pattern) (ha : d263556 p = 1) (hb : d324199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263551 q = 1) (hb : d324194 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263551, d324194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263551, d324194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98152 q ha hb
  have h2 (q : Pattern) (ha : d263552 q = 1) (hb : d324195 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263552, d324195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263552, d324195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263553 q = 1) (hb : d324196 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263553, d324196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263553, d324196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263554 q = 1) (hb : d324197 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263554, d324197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263554, d324197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263555 q = 1) (hb : d324198 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263555, d324198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263555, d324198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263556 q = 1) (hb : d324199 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263556, d324199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263556, d324199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98154 (p : Pattern) (ha : d263768 p = 1) (hb : d323771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263699 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d263727 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d263664 q = 1) (hb : d323766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263664, d323766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98029 q ha hb
    | true =>
      simp only [d263664, d323766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98030 q ha hb
  have h5 (q : Pattern) (ha : d263728 q = 1) (hb : d323767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263728, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263728, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d263764 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d263765 q = 1) (hb : d323768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263765, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263765, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d263766 q = 1) (hb : d323769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263766, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263766, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263767 q = 1) (hb : d323770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263767, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263767, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263768 q = 1) (hb : d323771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263768, d323771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263768, d323771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98155 (p : Pattern) (ha : d263790 p = 1) (hb : d323781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263690 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263699 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263664 q = 1) (hb : d323766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263664, d323766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98029 q ha hb
    | true =>
      simp only [d263664, d323766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98030 q ha hb
  have h4 (q : Pattern) (ha : d263728 q = 1) (hb : d323767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263728, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263728, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d263764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d263765 q = 1) (hb : d323768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263765, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263765, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d263766 q = 1) (hb : d323769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263766, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263766, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263767 q = 1) (hb : d323770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263767, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263767, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263774 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d263779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d263782 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d263674 q = 1) (hb : d323776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263674, d323776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98032 q ha hb
    | true =>
      simp only [d263674, d323776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98033 q ha hb
  have h13 (q : Pattern) (ha : d263783 q = 1) (hb : d323777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263783, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d263783, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263786 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263787 q = 1) (hb : d323778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263787, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263787, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263788 q = 1) (hb : d323779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263788, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d263788, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263789 q = 1) (hb : d323780 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263789, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d263789, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d263790 q = 1) (hb : d323781 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263790, d323781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263790, d323781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98156 (p : Pattern) (ha : d263815 p = 1) (hb : d324206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263782 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263674 q = 1) (hb : d323776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263674, d323776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98032 q ha hb
    | true =>
      simp only [d263674, d323776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98033 q ha hb
  have h3 (q : Pattern) (ha : d263783 q = 1) (hb : d323777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263783, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263783, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263786 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263787 q = 1) (hb : d323778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263787, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263787, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263813 q = 1) (hb : d323779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263813, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263813, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263814 q = 1) (hb : d323780 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263814, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263814, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263815 q = 1) (hb : d324206 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263815, d324206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263815, d324206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98157 (p : Pattern) (ha : d263905 p = 1) (hb : d323947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263863 q = 1) (hb : d323932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263863, d323932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98065 q ha hb
    | true =>
      simp only [d263863, d323932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98067 q ha hb
  have h2 (q : Pattern) (ha : d263864 q = 1) (hb : d323933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263864, d323933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263864, d323933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263865 q = 1) (hb : d323934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263865, d323934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263865, d323934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263872 q = 1) (hb : d323937 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263872, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98067 q ha hb
    | true =>
      simp only [d263872, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98068 q ha hb
  have h5 (q : Pattern) (ha : d263873 q = 1) (hb : d323938 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263873, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263873, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263874 q = 1) (hb : d323939 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263874, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263874, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263875 q = 1) (hb : d323940 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263875, d323940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263875, d323940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263891 q = 1) (hb : d323937 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263891, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98067 q ha hb
    | true =>
      simp only [d263891, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98072 q ha hb
  have h9 (q : Pattern) (ha : d263892 q = 1) (hb : d323938 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263892, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263892, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263893 q = 1) (hb : d323939 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263893, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263893, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263894 q = 1) (hb : d323945 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263894, d323945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263894, d323945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263904 q = 1) (hb : d323946 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263904, d323946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263904, d323946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263905 q = 1) (hb : d323947 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263905, d323947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263905, d323947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro98158 (p : Pattern) (ha : d263911 p = 1) (hb : d323961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263906 q = 1) (hb : d323948 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263906, d323948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98157 q ha hb
    | true =>
      simp only [d263906, d323948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263907 q = 1) (hb : d323949 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263907, d323949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263907, d323949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263897 q = 1) (hb : d323956 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263897, d323956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98073 q ha hb
    | true =>
      simp only [d263897, d323956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263898 q = 1) (hb : d323957 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263898, d323957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263898, d323957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263908 q = 1) (hb : d323958 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263908, d323958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263908, d323958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263909 q = 1) (hb : d323959 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263909, d323959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263909, d323959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263910 q = 1) (hb : d323960 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263910, d323960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263910, d323960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263911 q = 1) (hb : d323961 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263911, d323961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263911, d323961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98159 (p : Pattern) (ha : d263928 p = 1) (hb : d323936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263857 q = 1) (hb : d323926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263857, d323926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263857, d323926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98022 q ha hb
  have h2 (q : Pattern) (ha : d263616 q = 1) (hb : d323733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98022 q ha hb
    | true =>
      simp only [d263616, d323733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263858 q = 1) (hb : d323927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263858, d323927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263858, d323927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263617 q = 1) (hb : d323734 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263617, d323734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263859 q = 1) (hb : d323928 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263859, d323928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263859, d323928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263860 q = 1) (hb : d323929 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263860, d323929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263860, d323929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263889 q = 1) (hb : d323935 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263889, d323935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263889, d323935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10412 q = 1) (hb : d263923 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d263923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66730 q ha hb
    | true =>
      simp only [d10412, d263923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10414 q = 1) (hb : d263924 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d263924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10414, d263924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15792 q = 1) (hb : d263925 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d263925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d263925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15793 q = 1) (hb : d263926 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d263926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15793, d263926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15794 q = 1) (hb : d263927 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d263927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15794, d263927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d263928 q = 1) (hb : d323936 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263928, d323936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263928, d323936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro98160 (p : Pattern) (ha : d263934 p = 1) (hb : d323955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263929 q = 1) (hb : d323937 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263929, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98067 q ha hb
    | true =>
      simp only [d263929, d323937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98159 q ha hb
  have h2 (q : Pattern) (ha : d263930 q = 1) (hb : d323938 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263930, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263930, d323938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263931 q = 1) (hb : d323939 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263931, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263931, d323939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263932 q = 1) (hb : d323945 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263932, d323945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263932, d323945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263933 q = 1) (hb : d323954 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263933, d323954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263933, d323954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263934 q = 1) (hb : d323955 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263934, d323955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263934, d323955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98161 (p : Pattern) (ha : d263940 p = 1) (hb : d323998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263935 q = 1) (hb : d323956 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263935, d323956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98160 q ha hb
    | true =>
      simp only [d263935, d323956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263936 q = 1) (hb : d323957 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263936, d323957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263936, d323957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263937 q = 1) (hb : d323995 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263937, d323995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263937, d323995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263938 q = 1) (hb : d323996 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263938, d323996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263938, d323996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263939 q = 1) (hb : d323997 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263939, d323997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263939, d323997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263940 q = 1) (hb : d323998 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263940, d323998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263940, d323998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98162 (p : Pattern) (ha : d263972 p = 1) (hb : d324217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263903 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263941 q = 1) (hb : d324212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263941, d324212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98158 q ha hb
    | true =>
      simp only [d263941, d324212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98161 q ha hb
  have h3 (q : Pattern) (ha : d263942 q = 1) (hb : d324213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263942, d324213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263942, d324213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263968 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263969 q = 1) (hb : d324214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263969, d324214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263969, d324214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263970 q = 1) (hb : d324215 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263970, d324215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263970, d324215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263971 q = 1) (hb : d324216 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263971, d324216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263971, d324216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263972 q = 1) (hb : d324217 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263972, d324217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263972, d324217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98163 (p : Pattern) (ha : d263989 p = 1) (hb : d324223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263682 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263791 q = 1) (hb : d323782 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263791, d323782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98154 q ha hb
    | true =>
      simp only [d263791, d323782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98155 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263810 q = 1) (hb : d323783 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263810, d323783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263810, d323783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263811 q = 1) (hb : d324204 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263811, d324204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263811, d324204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263812 q = 1) (hb : d324205 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263812, d324205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263812, d324205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263816 q = 1) (hb : d324207 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263816, d324207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263816, d324207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98156 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263818 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263819 q = 1) (hb : d324208 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263819, d324208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263819, d324208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263820 q = 1) (hb : d324209 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263820, d324209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263820, d324209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263821 q = 1) (hb : d324210 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263821, d324210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263821, d324210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263822 q = 1) (hb : d324211 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263822, d324211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263822, d324211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263973 q = 1) (hb : d324218 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263973, d324218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263973, d324218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98162 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263984 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263985 q = 1) (hb : d324219 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263985, d324219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263985, d324219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263986 q = 1) (hb : d324220 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263986, d324220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263986, d324220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263987 q = 1) (hb : d324221 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263987, d324221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263987, d324221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263988 q = 1) (hb : d324222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263988, d324222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263988, d324222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263989 q = 1) (hb : d324223 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263989, d324223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263989, d324223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98164 (p : Pattern) (ha : d263995 p = 1) (hb : d324229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263990 q = 1) (hb : d324224 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263990, d324224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263990, d324224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98163 q ha hb
  have h2 (q : Pattern) (ha : d263991 q = 1) (hb : d324225 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263991, d324225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263991, d324225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263992 q = 1) (hb : d324226 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263992, d324226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263992, d324226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263993 q = 1) (hb : d324227 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263993, d324227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263993, d324227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263994 q = 1) (hb : d324228 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263994, d324228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263994, d324228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263995 q = 1) (hb : d324229 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263995, d324229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263995, d324229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98165 (p : Pattern) (ha : d264001 p = 1) (hb : d324235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d262468 q = 1) (hb : d324116 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262468, d324116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98129 q ha hb
    | true =>
      simp only [d262468, d324116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98135 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262753 q = 1) (hb : d324143 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262753, d324143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262753, d324143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98141 q ha hb
  have h3 (q : Pattern) (ha : d262754 q = 1) (hb : d324144 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d262754, d324144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d262754, d324144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263147 q = 1) (hb : d324171 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263147, d324171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263147, d324171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98147 q ha hb
  have h5 (q : Pattern) (ha : d263148 q = 1) (hb : d324172 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263148, d324172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263148, d324172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263149 q = 1) (hb : d324173 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263149, d324173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263149, d324173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263557 q = 1) (hb : d324200 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263557, d324200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263557, d324200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98153 q ha hb
  have h8 (q : Pattern) (ha : d263558 q = 1) (hb : d324201 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263558, d324201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263558, d324201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263559 q = 1) (hb : d324202 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263559, d324202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263559, d324202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263560 q = 1) (hb : d324203 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263560, d324203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263560, d324203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263996 q = 1) (hb : d324230 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263996, d324230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263996, d324230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98164 q ha hb
  have h12 (q : Pattern) (ha : d263997 q = 1) (hb : d324231 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263997, d324231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263997, d324231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263998 q = 1) (hb : d324232 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263998, d324232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263998, d324232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263999 q = 1) (hb : d324233 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263999, d324233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263999, d324233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d264000 q = 1) (hb : d324234 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d264000, d324234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d264000, d324234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d264001 q = 1) (hb : d324235 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d264001, d324235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d264001, d324235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro98166 (p : Pattern) (ha : d264007 p = 1) (hb : d324241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264002 q = 1) (hb : d324236 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d264002, d324236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98165 q ha hb
    | true =>
      simp only [d264002, d324236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264003 q = 1) (hb : d324237 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d264003, d324237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264003, d324237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264004 q = 1) (hb : d324238 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d264004, d324238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264004, d324238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264005 q = 1) (hb : d324239 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d264005, d324239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264005, d324239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264006 q = 1) (hb : d324240 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d264006, d324240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264006, d324240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264007 q = 1) (hb : d324241 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d264007, d324241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264007, d324241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98167 (p : Pattern) (ha : d264013 p = 1) (hb : d324247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264008 q = 1) (hb : d324242 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d264008, d324242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98166 q ha hb
    | true =>
      simp only [d264008, d324242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264009 q = 1) (hb : d324243 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d264009, d324243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264009, d324243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264010 q = 1) (hb : d324244 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d264010, d324244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264010, d324244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264011 q = 1) (hb : d324245 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d264011, d324245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264011, d324245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264012 q = 1) (hb : d324246 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d264012, d324246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264012, d324246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264013 q = 1) (hb : d324247 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d264013, d324247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264013, d324247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98168 (p : Pattern) (ha : d264019 p = 1) (hb : d324253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264014 q = 1) (hb : d324248 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d264014, d324248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98167 q ha hb
    | true =>
      simp only [d264014, d324248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264015 q = 1) (hb : d324249 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d264015, d324249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264015, d324249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264016 q = 1) (hb : d324250 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d264016, d324250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264016, d324250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264017 q = 1) (hb : d324251 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d264017, d324251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264017, d324251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264018 q = 1) (hb : d324252 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d264018, d324252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264018, d324252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264019 q = 1) (hb : d324253 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d264019, d324253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264019, d324253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98169 (p : Pattern) (ha : d264025 p = 1) (hb : d324259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264020 q = 1) (hb : d324254 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d264020, d324254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98168 q ha hb
    | true =>
      simp only [d264020, d324254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264021 q = 1) (hb : d324255 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d264021, d324255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264021, d324255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264022 q = 1) (hb : d324256 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d264022, d324256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264022, d324256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264023 q = 1) (hb : d324257 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d264023, d324257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264023, d324257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264024 q = 1) (hb : d324258 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d264024, d324258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264024, d324258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264025 q = 1) (hb : d324259 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d264025, d324259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264025, d324259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98170 (p : Pattern) (ha : d264031 p = 1) (hb : d324265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264026 q = 1) (hb : d324260 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d264026, d324260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98169 q ha hb
    | true =>
      simp only [d264026, d324260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264027 q = 1) (hb : d324261 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d264027, d324261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264027, d324261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264028 q = 1) (hb : d324262 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d264028, d324262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264028, d324262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264029 q = 1) (hb : d324263 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d264029, d324263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264029, d324263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264030 q = 1) (hb : d324264 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d264030, d324264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264030, d324264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264031 q = 1) (hb : d324265 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d264031, d324265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264031, d324265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98171 (p : Pattern) (ha : d264037 p = 1) (hb : d324271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264032 q = 1) (hb : d324266 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d264032, d324266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98170 q ha hb
    | true =>
      simp only [d264032, d324266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264033 q = 1) (hb : d324267 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d264033, d324267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264033, d324267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264034 q = 1) (hb : d324268 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d264034, d324268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264034, d324268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264035 q = 1) (hb : d324269 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d264035, d324269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264035, d324269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264036 q = 1) (hb : d324270 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d264036, d324270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264036, d324270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264037 q = 1) (hb : d324271 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d264037, d324271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264037, d324271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98172 (p : Pattern) (ha : d264043 p = 1) (hb : d324277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264038 q = 1) (hb : d324272 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d264038, d324272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98171 q ha hb
    | true =>
      simp only [d264038, d324272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264039 q = 1) (hb : d324273 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d264039, d324273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264039, d324273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264040 q = 1) (hb : d324274 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d264040, d324274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264040, d324274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264041 q = 1) (hb : d324275 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d264041, d324275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264041, d324275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264042 q = 1) (hb : d324276 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d264042, d324276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264042, d324276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264043 q = 1) (hb : d324277 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d264043, d324277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264043, d324277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98173 (p : Pattern) (ha : d265953 p = 1) (hb : d322345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33325 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33360 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d322281 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265949 q = 1) (hb : d322341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d265949, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d33394 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265950 q = 1) (hb : d322342 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265950, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d265951 q = 1) (hb : d322343 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265951, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265952 q = 1) (hb : d322344 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265952, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265953 q = 1) (hb : d322345 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265953, d322345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265953, d322345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98174 (p : Pattern) (ha : d265958 p = 1) (hb : d322352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d322281 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d265949 q = 1) (hb : d322341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265949, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d33394 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d265950 q = 1) (hb : d322342 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265950, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d265951 q = 1) (hb : d322343 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265951, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265952 q = 1) (hb : d322344 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265952, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d33403 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d33407 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d33409 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d322288 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d265954 q = 1) (hb : d322348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d265954, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33415 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265955 q = 1) (hb : d322349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265955, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265956 q = 1) (hb : d322350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265956, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d265956, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265957 q = 1) (hb : d322351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265957, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d265957, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265958 q = 1) (hb : d322352 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265958, d322352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265958, d322352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98175 (p : Pattern) (ha : d265965 p = 1) (hb : d324067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d322288 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265954 q = 1) (hb : d322348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265954, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33415 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265955 q = 1) (hb : d322349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265955, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d265963 q = 1) (hb : d322350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265963, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265963, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265964 q = 1) (hb : d322351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265964, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265964, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265965 q = 1) (hb : d324067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265965, d324067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265965, d324067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98176 (p : Pattern) (ha : d265975 p = 1) (hb : d324077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33457 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d322324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265971 q = 1) (hb : d324073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265971, d324073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265971, d324073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265972 q = 1) (hb : d324074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265972, d324074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265972, d324074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d265973 q = 1) (hb : d324075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265973, d324075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265973, d324075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265974 q = 1) (hb : d324076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265974, d324076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265974, d324076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265975 q = 1) (hb : d324077 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265975, d324077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265975, d324077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98177 (p : Pattern) (ha : d265981 p = 1) (hb : d324083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265959 q = 1) (hb : d322353 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265959, d322353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98173 q ha hb
    | true =>
      simp only [d265959, d322353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98174 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265960 q = 1) (hb : d322354 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265960, d322354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265960, d322354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265961 q = 1) (hb : d324065 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265961, d324065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265961, d324065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265962 q = 1) (hb : d324066 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265962, d324066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265962, d324066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265966 q = 1) (hb : d324068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265966, d324068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265966, d324068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98175 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d265967 q = 1) (hb : d324069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265967, d324069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265967, d324069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d265968 q = 1) (hb : d324070 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265968, d324070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265968, d324070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d265969 q = 1) (hb : d324071 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265969, d324071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265969, d324071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d265970 q = 1) (hb : d324072 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265970, d324072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265970, d324072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265976 q = 1) (hb : d324078 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265976, d324078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265976, d324078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98176 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265977 q = 1) (hb : d324079 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265977, d324079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265977, d324079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265978 q = 1) (hb : d324080 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265978, d324080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265978, d324080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d265979 q = 1) (hb : d324081 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265979, d324081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d265979, d324081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d265980 q = 1) (hb : d324082 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265980, d324082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d265980, d324082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d265981 q = 1) (hb : d324083 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265981, d324083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265981, d324083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98178 (p : Pattern) (ha : d265987 p = 1) (hb : d324089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d265944 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d265944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d265944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66749 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d265945 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d265945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d265945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d265946 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d265946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d265946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d265947 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d265947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d265947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d265948 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d265948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d265948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265982 q = 1) (hb : d324084 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265982, d324084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265982, d324084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98177 q ha hb
  have h8 (q : Pattern) (ha : d265983 q = 1) (hb : d324085 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265983, d324085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265983, d324085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265984 q = 1) (hb : d324086 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265984, d324086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265984, d324086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265985 q = 1) (hb : d324087 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265985, d324087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265985, d324087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d265986 q = 1) (hb : d324088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265986, d324088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265986, d324088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265987 q = 1) (hb : d324089 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d265987, d324089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d265987, d324089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro98179 (p : Pattern) (ha : d265992 p = 1) (hb : d322515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33552 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33602 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d322510 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265988 q = 1) (hb : d322511 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d265988, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d33653 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265989 q = 1) (hb : d322512 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265989, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d265990 q = 1) (hb : d322513 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265990, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265991 q = 1) (hb : d322514 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265991, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265992 q = 1) (hb : d322515 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265992, d322515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265992, d322515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98180 (p : Pattern) (ha : d265997 p = 1) (hb : d322525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33543 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33552 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33602 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d322510 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d265988 q = 1) (hb : d322511 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265988, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d33653 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d265989 q = 1) (hb : d322512 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265989, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d265990 q = 1) (hb : d322513 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265990, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265991 q = 1) (hb : d322514 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265991, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d33663 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d33668 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d33670 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d322520 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d265993 q = 1) (hb : d322521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d265993, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33677 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265994 q = 1) (hb : d322522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265994, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265995 q = 1) (hb : d322523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265995, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d265995, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265996 q = 1) (hb : d322524 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265996, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d265996, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265997 q = 1) (hb : d322525 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265997, d322525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265997, d322525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98181 (p : Pattern) (ha : d266004 p = 1) (hb : d324092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d322520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265993 q = 1) (hb : d322521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265993, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33677 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265994 q = 1) (hb : d322522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265994, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266002 q = 1) (hb : d322523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266002, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266002, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266003 q = 1) (hb : d322524 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266003, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266003, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266004 q = 1) (hb : d324092 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266004, d324092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266004, d324092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98182 (p : Pattern) (ha : d266014 p = 1) (hb : d324103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d324098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266010 q = 1) (hb : d324099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266010, d324099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266010, d324099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33793 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266011 q = 1) (hb : d324100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266011, d324100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266011, d324100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266012 q = 1) (hb : d324101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266012, d324101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266012, d324101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266013 q = 1) (hb : d324102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266013, d324102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266013, d324102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266014 q = 1) (hb : d324103 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266014, d324103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266014, d324103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98183 (p : Pattern) (ha : d266020 p = 1) (hb : d324109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33535 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265998 q = 1) (hb : d322526 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265998, d322526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98179 q ha hb
    | true =>
      simp only [d265998, d322526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98180 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33695 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265999 q = 1) (hb : d322527 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265999, d322527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265999, d322527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266000 q = 1) (hb : d324090 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266000, d324090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266000, d324090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266001 q = 1) (hb : d324091 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266001, d324091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266001, d324091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266005 q = 1) (hb : d324093 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266005, d324093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266005, d324093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98181 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d33704 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266006 q = 1) (hb : d324094 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266006, d324094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266006, d324094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266007 q = 1) (hb : d324095 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266007, d324095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266007, d324095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266008 q = 1) (hb : d324096 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266008, d324096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266008, d324096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266009 q = 1) (hb : d324097 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266009, d324097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266009, d324097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266015 q = 1) (hb : d324104 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266015, d324104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266015, d324104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98182 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33809 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266016 q = 1) (hb : d324105 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266016, d324105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266016, d324105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266017 q = 1) (hb : d324106 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266017, d324106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266017, d324106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266018 q = 1) (hb : d324107 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266018, d324107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266018, d324107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266019 q = 1) (hb : d324108 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266019, d324108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266019, d324108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266020 q = 1) (hb : d324109 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266020, d324109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266020, d324109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98184 (p : Pattern) (ha : d266026 p = 1) (hb : d324115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266021 q = 1) (hb : d324110 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266021, d324110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266021, d324110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98183 q ha hb
  have h2 (q : Pattern) (ha : d266022 q = 1) (hb : d324111 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266022, d324111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266022, d324111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266023 q = 1) (hb : d324112 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266023, d324112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266023, d324112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266024 q = 1) (hb : d324113 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266024, d324113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266024, d324113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266025 q = 1) (hb : d324114 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266025, d324114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266025, d324114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266026 q = 1) (hb : d324115 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266026, d324115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266026, d324115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98185 (p : Pattern) (ha : d266032 p = 1) (hb : d322772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33892 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33949 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d322767 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266028 q = 1) (hb : d322768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d322768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266028, d322768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d34023 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266029 q = 1) (hb : d322769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d322769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266029, d322769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266030 q = 1) (hb : d322770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d322770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266030, d322770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266031 q = 1) (hb : d322771 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d322771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266031, d322771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266032 q = 1) (hb : d322772 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266032, d322772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266032, d322772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98186 (p : Pattern) (ha : d266037 p = 1) (hb : d322782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33883 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33892 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33949 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d322767 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266028 q = 1) (hb : d322768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d322768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266028, d322768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d34023 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266029 q = 1) (hb : d322769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d322769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266029, d322769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266030 q = 1) (hb : d322770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d322770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266030, d322770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266031 q = 1) (hb : d322771 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d322771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266031, d322771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d34033 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d34038 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d34040 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d322777 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266033 q = 1) (hb : d322778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d322778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266033, d322778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34047 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266034 q = 1) (hb : d322779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d322779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266034, d322779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266035 q = 1) (hb : d322780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266035, d322780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266035, d322780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266036 q = 1) (hb : d322781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266036, d322781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266036, d322781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266037 q = 1) (hb : d322782 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266037, d322782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266037, d322782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98187 (p : Pattern) (ha : d266044 p = 1) (hb : d324119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d322777 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266033 q = 1) (hb : d322778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d322778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266033, d322778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34047 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266034 q = 1) (hb : d322779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d322779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266034, d322779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266042 q = 1) (hb : d322780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266042, d322780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266042, d322780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266043 q = 1) (hb : d322781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266043, d322781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266043, d322781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266044 q = 1) (hb : d324119 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266044, d324119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266044, d324119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98188 (p : Pattern) (ha : d266054 p = 1) (hb : d324130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d324125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266050 q = 1) (hb : d324126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266050, d324126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266050, d324126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34195 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266051 q = 1) (hb : d324127 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266051, d324127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266051, d324127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266052 q = 1) (hb : d324128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266052, d324128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266052, d324128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266053 q = 1) (hb : d324129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266053, d324129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266053, d324129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266054 q = 1) (hb : d324130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266054, d324130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266054, d324130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98189 (p : Pattern) (ha : d266060 p = 1) (hb : d324136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266038 q = 1) (hb : d322783 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266038, d322783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98185 q ha hb
    | true =>
      simp only [d266038, d322783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98186 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34065 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266039 q = 1) (hb : d322784 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266039, d322784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266039, d322784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266040 q = 1) (hb : d324117 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266040, d324117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266040, d324117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266041 q = 1) (hb : d324118 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266041, d324118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266041, d324118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266045 q = 1) (hb : d324120 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266045, d324120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266045, d324120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98187 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d34074 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266046 q = 1) (hb : d324121 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266046, d324121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266046, d324121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266047 q = 1) (hb : d324122 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266047, d324122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266047, d324122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266048 q = 1) (hb : d324123 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266048, d324123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266048, d324123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266049 q = 1) (hb : d324124 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266049, d324124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266049, d324124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266055 q = 1) (hb : d324131 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266055, d324131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266055, d324131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98188 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34211 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266056 q = 1) (hb : d324132 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266056, d324132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266056, d324132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266057 q = 1) (hb : d324133 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266057, d324133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266057, d324133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266058 q = 1) (hb : d324134 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266058, d324134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266058, d324134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266059 q = 1) (hb : d324135 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266059, d324135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266059, d324135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266060 q = 1) (hb : d324136 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266060, d324136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266060, d324136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98190 (p : Pattern) (ha : d266066 p = 1) (hb : d324142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266061 q = 1) (hb : d324137 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266061, d324137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266061, d324137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98189 q ha hb
  have h2 (q : Pattern) (ha : d266062 q = 1) (hb : d324138 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266062, d324138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266062, d324138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266063 q = 1) (hb : d324139 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266063, d324139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266063, d324139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266064 q = 1) (hb : d324140 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266064, d324140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266064, d324140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266065 q = 1) (hb : d324141 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266065, d324141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266065, d324141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266066 q = 1) (hb : d324142 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266066, d324142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266066, d324142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98191 (p : Pattern) (ha : d266073 p = 1) (hb : d323085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34342 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d34415 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d323080 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266069 q = 1) (hb : d323081 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266069, d323081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266069, d323081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d34534 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266070 q = 1) (hb : d323082 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266070, d323082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266070, d323082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266071 q = 1) (hb : d323083 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266071, d323083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266071, d323083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266072 q = 1) (hb : d323084 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266072, d323084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266072, d323084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266073 q = 1) (hb : d323085 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266073, d323085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266073, d323085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98192 (p : Pattern) (ha : d266078 p = 1) (hb : d323095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34415 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d323080 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266069 q = 1) (hb : d323081 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266069, d323081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266069, d323081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d34534 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266070 q = 1) (hb : d323082 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266070, d323082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266070, d323082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266071 q = 1) (hb : d323083 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266071, d323083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266071, d323083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266072 q = 1) (hb : d323084 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266072, d323084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266072, d323084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d34544 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d34549 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d34551 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d323090 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266074 q = 1) (hb : d323091 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266074, d323091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266074, d323091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34558 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266075 q = 1) (hb : d323092 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266075, d323092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266075, d323092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266076 q = 1) (hb : d323093 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266076, d323093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266076, d323093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266077 q = 1) (hb : d323094 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266077, d323094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266077, d323094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266078 q = 1) (hb : d323095 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266078, d323095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266078, d323095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98193 (p : Pattern) (ha : d266085 p = 1) (hb : d324147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34551 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d323090 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266074 q = 1) (hb : d323091 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266074, d323091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266074, d323091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34558 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266075 q = 1) (hb : d323092 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266075, d323092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266075, d323092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266083 q = 1) (hb : d323093 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266083, d323093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266083, d323093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266084 q = 1) (hb : d323094 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266084, d323094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266084, d323094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266085 q = 1) (hb : d324147 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266085, d324147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266085, d324147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98194 (p : Pattern) (ha : d266095 p = 1) (hb : d324158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d324153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266091 q = 1) (hb : d324154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266091, d324154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266091, d324154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34751 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266092 q = 1) (hb : d324155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266092, d324155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266092, d324155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266093 q = 1) (hb : d324156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266093, d324156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266093, d324156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266094 q = 1) (hb : d324157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266094, d324157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266094, d324157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266095 q = 1) (hb : d324158 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266095, d324158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266095, d324158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98195 (p : Pattern) (ha : d266101 p = 1) (hb : d324164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266079 q = 1) (hb : d323096 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266079, d323096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98191 q ha hb
    | true =>
      simp only [d266079, d323096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98192 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34576 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266080 q = 1) (hb : d323097 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266080, d323097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266080, d323097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266081 q = 1) (hb : d324145 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266081, d324145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266081, d324145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266082 q = 1) (hb : d324146 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266082, d324146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266082, d324146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266086 q = 1) (hb : d324148 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266086, d324148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266086, d324148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98193 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d34585 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266087 q = 1) (hb : d324149 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266087, d324149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266087, d324149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266088 q = 1) (hb : d324150 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266088, d324150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266088, d324150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266089 q = 1) (hb : d324151 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266089, d324151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266089, d324151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266090 q = 1) (hb : d324152 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266090, d324152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266090, d324152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266096 q = 1) (hb : d324159 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266096, d324159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266096, d324159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98194 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34767 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266097 q = 1) (hb : d324160 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266097, d324160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266097, d324160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266098 q = 1) (hb : d324161 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266098, d324161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266098, d324161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266099 q = 1) (hb : d324162 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266099, d324162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266099, d324162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266100 q = 1) (hb : d324163 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266100, d324163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266100, d324163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266101 q = 1) (hb : d324164 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266101, d324164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266101, d324164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98196 (p : Pattern) (ha : d266107 p = 1) (hb : d324170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266102 q = 1) (hb : d324165 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266102, d324165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266102, d324165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98195 q ha hb
  have h2 (q : Pattern) (ha : d266103 q = 1) (hb : d324166 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266103, d324166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266103, d324166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266104 q = 1) (hb : d324167 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266104, d324167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266104, d324167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266105 q = 1) (hb : d324168 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266105, d324168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266105, d324168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266106 q = 1) (hb : d324169 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266106, d324169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266106, d324169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266107 q = 1) (hb : d324170 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266107, d324170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266107, d324170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98197 (p : Pattern) (ha : d266115 p = 1) (hb : d323437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34917 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d34963 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d323432 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266111 q = 1) (hb : d323433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266111, d323433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266111, d323433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d35102 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266112 q = 1) (hb : d323434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266112, d323434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266112, d323434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266113 q = 1) (hb : d323435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266113, d323435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266113, d323435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266114 q = 1) (hb : d323436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266114, d323436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266114, d323436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266115 q = 1) (hb : d323437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266115, d323437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266115, d323437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98198 (p : Pattern) (ha : d266120 p = 1) (hb : d323447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34963 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d323432 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266111 q = 1) (hb : d323433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266111, d323433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266111, d323433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d35102 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266112 q = 1) (hb : d323434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266112, d323434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266112, d323434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266113 q = 1) (hb : d323435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266113, d323435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266113, d323435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266114 q = 1) (hb : d323436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266114, d323436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266114, d323436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d35112 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d35117 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d35119 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d323442 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266116 q = 1) (hb : d323443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266116, d323443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266116, d323443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35126 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266117 q = 1) (hb : d323444 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266117, d323444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266117, d323444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266118 q = 1) (hb : d323445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266118, d323445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266118, d323445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266119 q = 1) (hb : d323446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266119, d323446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266119, d323446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266120 q = 1) (hb : d323447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266120, d323447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266120, d323447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98199 (p : Pattern) (ha : d266127 p = 1) (hb : d324176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d323442 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266116 q = 1) (hb : d323443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266116, d323443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266116, d323443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266117 q = 1) (hb : d323444 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266117, d323444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266117, d323444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266125 q = 1) (hb : d323445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266125, d323445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266125, d323445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266126 q = 1) (hb : d323446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266126, d323446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266126, d323446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266127 q = 1) (hb : d324176 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266127, d324176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266127, d324176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98200 (p : Pattern) (ha : d266137 p = 1) (hb : d324187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d324182 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266133 q = 1) (hb : d324183 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266133, d324183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266133, d324183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35330 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266134 q = 1) (hb : d324184 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266134, d324184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266134, d324184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266135 q = 1) (hb : d324185 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266135, d324185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266135, d324185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266136 q = 1) (hb : d324186 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266136, d324186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266136, d324186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266137 q = 1) (hb : d324187 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266137, d324187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266137, d324187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98201 (p : Pattern) (ha : d266143 p = 1) (hb : d324193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34900 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266121 q = 1) (hb : d323448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266121, d323448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98197 q ha hb
    | true =>
      simp only [d266121, d323448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98198 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266122 q = 1) (hb : d323449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266122, d323449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266122, d323449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266123 q = 1) (hb : d324174 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266123, d324174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266123, d324174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266124 q = 1) (hb : d324175 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266124, d324175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266124, d324175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266128 q = 1) (hb : d324177 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266128, d324177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266128, d324177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98199 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d35153 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266129 q = 1) (hb : d324178 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266129, d324178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266129, d324178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266130 q = 1) (hb : d324179 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266130, d324179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266130, d324179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266131 q = 1) (hb : d324180 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266131, d324180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266131, d324180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266132 q = 1) (hb : d324181 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266132, d324181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266132, d324181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266138 q = 1) (hb : d324188 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266138, d324188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266138, d324188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98200 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35346 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266139 q = 1) (hb : d324189 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266139, d324189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266139, d324189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266140 q = 1) (hb : d324190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266140, d324190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266140, d324190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266141 q = 1) (hb : d324191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266141, d324191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266141, d324191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266142 q = 1) (hb : d324192 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266142, d324192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266142, d324192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266143 q = 1) (hb : d324193 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266143, d324193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266143, d324193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98202 (p : Pattern) (ha : d266149 p = 1) (hb : d324199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266144 q = 1) (hb : d324194 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266144, d324194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266144, d324194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98201 q ha hb
  have h2 (q : Pattern) (ha : d266145 q = 1) (hb : d324195 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266145, d324195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266145, d324195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266146 q = 1) (hb : d324196 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266146, d324196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266146, d324196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266147 q = 1) (hb : d324197 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266147, d324197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266147, d324197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266148 q = 1) (hb : d324198 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266148, d324198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266148, d324198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266149 q = 1) (hb : d324199 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266149, d324199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266149, d324199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98203 (p : Pattern) (ha : d266158 p = 1) (hb : d323771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35491 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d35528 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d323766 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266154 q = 1) (hb : d323767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266154, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266154, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d35669 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266155 q = 1) (hb : d323768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266155, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266155, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266156 q = 1) (hb : d323769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266156, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266156, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266157 q = 1) (hb : d323770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266157, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266157, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266158 q = 1) (hb : d323771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266158, d323771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266158, d323771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98204 (p : Pattern) (ha : d266163 p = 1) (hb : d323781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d35491 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35500 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35528 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d323766 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266154 q = 1) (hb : d323767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266154, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266154, d323767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d35669 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266155 q = 1) (hb : d323768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266155, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266155, d323768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266156 q = 1) (hb : d323769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266156, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266156, d323769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266157 q = 1) (hb : d323770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266157, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266157, d323770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d35679 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d35684 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d35687 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d323776 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266159 q = 1) (hb : d323777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266159, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266159, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35694 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266160 q = 1) (hb : d323778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266160, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266160, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266161 q = 1) (hb : d323779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266161, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266161, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266162 q = 1) (hb : d323780 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266162, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266162, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266163 q = 1) (hb : d323781 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266163, d323781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266163, d323781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98205 (p : Pattern) (ha : d266170 p = 1) (hb : d324206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d323776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266159 q = 1) (hb : d323777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266159, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266159, d323777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35694 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266160 q = 1) (hb : d323778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266160, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266160, d323778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266168 q = 1) (hb : d323779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266168, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266168, d323779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266169 q = 1) (hb : d323780 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266169, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266169, d323780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266170 q = 1) (hb : d324206 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266170, d324206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266170, d324206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98206 (p : Pattern) (ha : d266180 p = 1) (hb : d324217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d324212 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266176 q = 1) (hb : d324213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266176, d324213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266176, d324213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35929 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266177 q = 1) (hb : d324214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266177, d324214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266177, d324214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266178 q = 1) (hb : d324215 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266178, d324215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266178, d324215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266179 q = 1) (hb : d324216 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266179, d324216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266179, d324216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266180 q = 1) (hb : d324217 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266180, d324217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266180, d324217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98207 (p : Pattern) (ha : d266186 p = 1) (hb : d324223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d35483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266164 q = 1) (hb : d323782 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266164, d323782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98203 q ha hb
    | true =>
      simp only [d266164, d323782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98204 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35717 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266165 q = 1) (hb : d323783 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266165, d323783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266165, d323783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266166 q = 1) (hb : d324204 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266166, d324204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266166, d324204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266167 q = 1) (hb : d324205 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266167, d324205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266167, d324205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266171 q = 1) (hb : d324207 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266171, d324207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266171, d324207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98205 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d35726 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266172 q = 1) (hb : d324208 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266172, d324208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266172, d324208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266173 q = 1) (hb : d324209 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266173, d324209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266173, d324209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266174 q = 1) (hb : d324210 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266174, d324210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266174, d324210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266175 q = 1) (hb : d324211 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266175, d324211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266175, d324211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266181 q = 1) (hb : d324218 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266181, d324218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266181, d324218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98206 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266182 q = 1) (hb : d324219 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266182, d324219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266182, d324219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266183 q = 1) (hb : d324220 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266183, d324220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266183, d324220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266184 q = 1) (hb : d324221 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266184, d324221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266184, d324221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266185 q = 1) (hb : d324222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266185, d324222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266185, d324222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266186 q = 1) (hb : d324223 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266186, d324223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266186, d324223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98208 (p : Pattern) (ha : d266192 p = 1) (hb : d324229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266187 q = 1) (hb : d324224 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266187, d324224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266187, d324224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98207 q ha hb
  have h2 (q : Pattern) (ha : d266188 q = 1) (hb : d324225 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266188, d324225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266188, d324225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266189 q = 1) (hb : d324226 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266189, d324226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266189, d324226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266190 q = 1) (hb : d324227 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266190, d324227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266190, d324227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266191 q = 1) (hb : d324228 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266191, d324228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266191, d324228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266192 q = 1) (hb : d324229 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266192, d324229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266192, d324229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98209 (p : Pattern) (ha : d266198 p = 1) (hb : d324235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d266027 q = 1) (hb : d324116 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266027, d324116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98178 q ha hb
    | true =>
      simp only [d266027, d324116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98184 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d266067 q = 1) (hb : d324143 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266067, d324143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266067, d324143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98190 q ha hb
  have h3 (q : Pattern) (ha : d266068 q = 1) (hb : d324144 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266068, d324144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266068, d324144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266108 q = 1) (hb : d324171 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266108, d324171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266108, d324171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98196 q ha hb
  have h5 (q : Pattern) (ha : d266109 q = 1) (hb : d324172 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266109, d324172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266109, d324172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266110 q = 1) (hb : d324173 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266110, d324173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266110, d324173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266150 q = 1) (hb : d324200 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266150, d324200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266150, d324200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98202 q ha hb
  have h8 (q : Pattern) (ha : d266151 q = 1) (hb : d324201 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266151, d324201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266151, d324201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266152 q = 1) (hb : d324202 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266152, d324202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266152, d324202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266153 q = 1) (hb : d324203 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d266153, d324203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266153, d324203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d266193 q = 1) (hb : d324230 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266193, d324230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266193, d324230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98208 q ha hb
  have h12 (q : Pattern) (ha : d266194 q = 1) (hb : d324231 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266194, d324231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266194, d324231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266195 q = 1) (hb : d324232 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266195, d324232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266195, d324232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266196 q = 1) (hb : d324233 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d266196, d324233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266196, d324233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d266197 q = 1) (hb : d324234 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d266197, d324234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266197, d324234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d266198 q = 1) (hb : d324235 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d266198, d324235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266198, d324235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro98210 (p : Pattern) (ha : d266204 p = 1) (hb : d324241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266199 q = 1) (hb : d324236 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d266199, d324236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98209 q ha hb
    | true =>
      simp only [d266199, d324236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266200 q = 1) (hb : d324237 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d266200, d324237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266200, d324237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266201 q = 1) (hb : d324238 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d266201, d324238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266201, d324238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266202 q = 1) (hb : d324239 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d266202, d324239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266202, d324239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266203 q = 1) (hb : d324240 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d266203, d324240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266203, d324240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266204 q = 1) (hb : d324241 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d266204, d324241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266204, d324241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98211 (p : Pattern) (ha : d266210 p = 1) (hb : d324247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266205 q = 1) (hb : d324242 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d266205, d324242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98210 q ha hb
    | true =>
      simp only [d266205, d324242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266206 q = 1) (hb : d324243 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d266206, d324243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266206, d324243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266207 q = 1) (hb : d324244 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d266207, d324244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266207, d324244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266208 q = 1) (hb : d324245 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d266208, d324245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266208, d324245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266209 q = 1) (hb : d324246 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d266209, d324246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266209, d324246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266210 q = 1) (hb : d324247 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d266210, d324247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266210, d324247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98212 (p : Pattern) (ha : d266216 p = 1) (hb : d324253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266211 q = 1) (hb : d324248 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d266211, d324248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98211 q ha hb
    | true =>
      simp only [d266211, d324248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266212 q = 1) (hb : d324249 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d266212, d324249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266212, d324249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266213 q = 1) (hb : d324250 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d266213, d324250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266213, d324250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266214 q = 1) (hb : d324251 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d266214, d324251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266214, d324251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266215 q = 1) (hb : d324252 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d266215, d324252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266215, d324252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266216 q = 1) (hb : d324253 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d266216, d324253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266216, d324253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98213 (p : Pattern) (ha : d266222 p = 1) (hb : d324259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266217 q = 1) (hb : d324254 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d266217, d324254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98212 q ha hb
    | true =>
      simp only [d266217, d324254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266218 q = 1) (hb : d324255 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d266218, d324255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266218, d324255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266219 q = 1) (hb : d324256 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d266219, d324256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266219, d324256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266220 q = 1) (hb : d324257 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d266220, d324257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266220, d324257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266221 q = 1) (hb : d324258 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d266221, d324258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266221, d324258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266222 q = 1) (hb : d324259 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d266222, d324259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266222, d324259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98214 (p : Pattern) (ha : d266228 p = 1) (hb : d324265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266223 q = 1) (hb : d324260 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d266223, d324260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98213 q ha hb
    | true =>
      simp only [d266223, d324260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266224 q = 1) (hb : d324261 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d266224, d324261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266224, d324261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266225 q = 1) (hb : d324262 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d266225, d324262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266225, d324262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266226 q = 1) (hb : d324263 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d266226, d324263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266226, d324263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266227 q = 1) (hb : d324264 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d266227, d324264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266227, d324264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266228 q = 1) (hb : d324265 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d266228, d324265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266228, d324265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98215 (p : Pattern) (ha : d266234 p = 1) (hb : d324271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266229 q = 1) (hb : d324266 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d266229, d324266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98214 q ha hb
    | true =>
      simp only [d266229, d324266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266230 q = 1) (hb : d324267 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d266230, d324267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266230, d324267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266231 q = 1) (hb : d324268 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d266231, d324268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266231, d324268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266232 q = 1) (hb : d324269 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d266232, d324269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266232, d324269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266233 q = 1) (hb : d324270 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d266233, d324270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266233, d324270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266234 q = 1) (hb : d324271 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d266234, d324271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266234, d324271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98216 (p : Pattern) (ha : d266240 p = 1) (hb : d324277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266235 q = 1) (hb : d324272 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d266235, d324272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98215 q ha hb
    | true =>
      simp only [d266235, d324272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266236 q = 1) (hb : d324273 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d266236, d324273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266236, d324273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266237 q = 1) (hb : d324274 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d266237, d324274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266237, d324274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266238 q = 1) (hb : d324275 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d266238, d324275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266238, d324275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266239 q = 1) (hb : d324276 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d266239, d324276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266239, d324276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266240 q = 1) (hb : d324277 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d266240, d324277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266240, d324277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98217 (p : Pattern) (ha : d39704 p = 1) (hb : d287734 p = 1) : d30106 p = 1 := by
  have h0 (q : Pattern) (ha : d30096 q = 1) (hb : d287734 q = 1) : d30096 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2040 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2058 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2058, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2042 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2043 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2059 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d287734 q = 1) : d2048 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2060 q = 1) (hb : d287734 q = 1) : d30103 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2060, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2060, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10408 q = 1) (hb : d287734 q = 1) : d10408 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32713 q = 1) (hb : d287734 q = 1) : d30104 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32713, d30104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32713, d30104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32714 q = 1) (hb : d287734 q = 1) : d30105 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32714, d30105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32714, d30105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39704 q = 1) (hb : d287734 q = 1) : d30106 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39704, d30106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39704, d30106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro98218 (p : Pattern) (ha : d39710 p = 1) (hb : d287734 p = 1) : d30112 p = 1 := by
  have h0 (q : Pattern) (ha : d30102 q = 1) (hb : d287734 q = 1) : d30102 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30101 q = 1) (hb : d287734 q = 1) : d30101 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d39705 q = 1) (hb : d287734 q = 1) : d30107 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d30107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98217 q ha hb
    | true =>
      simp only [d39705, d30107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39706 q = 1) (hb : d287734 q = 1) : d30108 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d30108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39706, d30108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d39707 q = 1) (hb : d287734 q = 1) : d30109 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39707, d30109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39707, d30109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39708 q = 1) (hb : d287734 q = 1) : d30110 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39708, d30110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39708, d30110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d39709 q = 1) (hb : d287734 q = 1) : d30111 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39709, d30111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39709, d30111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39710 q = 1) (hb : d287734 q = 1) : d30112 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39710, d30112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39710, d30112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98219 (p : Pattern) (ha : d39716 p = 1) (hb : d287734 p = 1) : d30115 p = 1 := by
  have h0 (q : Pattern) (ha : d30086 q = 1) (hb : d287734 q = 1) : d30086 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30083 q = 1) (hb : d287734 q = 1) : d30083 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2039 q = 1) (hb : d253269 q = 1) : d2039 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2046 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d39711 q = 1) (hb : d287734 q = 1) : d30092 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d39711, d287734, d30092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39711, d287734, d30092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d39712 q = 1) (hb : d287734 q = 1) : d30093 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d39712, d30093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39712, d30093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39713 q = 1) (hb : d287734 q = 1) : d30094 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d39713, d30094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39713, d30094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30103 q = 1) (hb : d287734 q = 1) : d30103 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d39714 q = 1) (hb : d287734 q = 1) : d30113 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d39714, d30113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39714, d30113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39715 q = 1) (hb : d287734 q = 1) : d30114 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d39715, d30114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39715, d30114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h11 (q : Pattern) (ha : d39716 q = 1) (hb : d287734 q = 1) : d30115 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39716, d30115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39716, d30115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98220 (p : Pattern) (ha : d39721 p = 1) (hb : d287734 p = 1) : d30120 p = 1 := by
  have h0 (q : Pattern) (ha : d30083 q = 1) (hb : d287734 q = 1) : d30083 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2039 q = 1) (hb : d253269 q = 1) : d2039 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2046 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d39711 q = 1) (hb : d287734 q = 1) : d30092 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d39711, d287734, d30092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39711, d287734, d30092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d39712 q = 1) (hb : d287734 q = 1) : d30093 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d39712, d30093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39712, d30093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39713 q = 1) (hb : d287734 q = 1) : d30094 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d39713, d30094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39713, d30094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30103 q = 1) (hb : d287734 q = 1) : d30103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d39714 q = 1) (hb : d287734 q = 1) : d30113 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d39714, d30113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39714, d30113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d39715 q = 1) (hb : d287734 q = 1) : d30114 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d39715, d30114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39715, d30114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d2040 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d2058 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2058, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d2042 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2043 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2043, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d2059 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2048 q = 1) (hb : d287734 q = 1) : d2048 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d2060 q = 1) (hb : d287734 q = 1) : d30103 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2060, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2060, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10408 q = 1) (hb : d287734 q = 1) : d10408 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d32713 q = 1) (hb : d287734 q = 1) : d30104 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32713, d30104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d32713, d30104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d32714 q = 1) (hb : d287734 q = 1) : d30105 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32714, d30105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32714, d30105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h21 (q : Pattern) (ha : d39721 q = 1) (hb : d287734 q = 1) : d30120 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39721, d30120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39721, d30120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro98221 (p : Pattern) (ha : d39728 p = 1) (hb : d287734 p = 1) : d30127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39717 q = 1) (hb : d287734 q = 1) : d30116 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39717, d30116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98219 q ha hb
    | true =>
      simp only [d39717, d30116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39718 q = 1) (hb : d287734 q = 1) : d30117 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39718, d30117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39718, d30117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39719 q = 1) (hb : d287734 q = 1) : d30118 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39719, d30118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39719, d30118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39720 q = 1) (hb : d287734 q = 1) : d30119 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39720, d30119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39720, d30119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39722 q = 1) (hb : d287734 q = 1) : d30121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d30121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98220 q ha hb
    | true =>
      simp only [d39722, d30121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39723 q = 1) (hb : d287734 q = 1) : d30122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d30122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39723, d30122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39724 q = 1) (hb : d287734 q = 1) : d30123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39724, d30123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39724, d30123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39725 q = 1) (hb : d287734 q = 1) : d30124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39725, d30124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39725, d30124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39726 q = 1) (hb : d287734 q = 1) : d30125 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39726, d30125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39726, d30125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39705 q = 1) (hb : d287734 q = 1) : d30107 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d30107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98217 q ha hb
    | true =>
      simp only [d39705, d30107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39706 q = 1) (hb : d287734 q = 1) : d30108 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d30108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39706, d30108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d39707 q = 1) (hb : d287734 q = 1) : d30109 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39707, d30109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39707, d30109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39708 q = 1) (hb : d287734 q = 1) : d30110 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39708, d30110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39708, d30110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d39727 q = 1) (hb : d287734 q = 1) : d30126 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39727, d30126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39727, d30126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39728 q = 1) (hb : d287734 q = 1) : d30127 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39728, d30127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39728, d30127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98222 (p : Pattern) (ha : d10411 p = 1) (hb : d287734 p = 1) : d30134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2058 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2058, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2042 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2043 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2043, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2059 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2076 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10408 q = 1) (hb : d287734 q = 1) : d10408 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10409 q = 1) (hb : d287734 q = 1) : d30132 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10409, d30132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10409, d30132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10410 q = 1) (hb : d287734 q = 1) : d30133 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10410, d30133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10410, d30133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h11 (q : Pattern) (ha : d10411 q = 1) (hb : d287734 q = 1) : d30134 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10411, d30134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10411, d30134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h11 p ha hb
theorem andIntro98223 (p : Pattern) (ha : d39733 p = 1) (hb : d287734 p = 1) : d30140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39722 q = 1) (hb : d287734 q = 1) : d30121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d30121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98220 q ha hb
    | true =>
      simp only [d39722, d30121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39723 q = 1) (hb : d287734 q = 1) : d30122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d30122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39723, d30122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39724 q = 1) (hb : d287734 q = 1) : d30123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39724, d30123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39724, d30123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39725 q = 1) (hb : d287734 q = 1) : d30124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39725, d30124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39725, d30124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39732 q = 1) (hb : d287734 q = 1) : d30131 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39732, d30131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39732, d30131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10412 q = 1) (hb : d287734 q = 1) : d30135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d30135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98222 q ha hb
    | true =>
      simp only [d10412, d30135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10414 q = 1) (hb : d287734 q = 1) : d30136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d30136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10414, d30136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15555 q = 1) (hb : d287734 q = 1) : d30137 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d30137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, d30137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15556 q = 1) (hb : d287734 q = 1) : d30138 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d30138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15556, d30138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15557 q = 1) (hb : d287734 q = 1) : d30139 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d30139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15557, d30139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39733 q = 1) (hb : d287734 q = 1) : d30140 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39733, d30140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39733, d30140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98224 (p : Pattern) (ha : d39740 p = 1) (hb : d287734 p = 1) : d30147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39729 q = 1) (hb : d287734 q = 1) : d30128 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39729, d30128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98218 q ha hb
    | true =>
      simp only [d39729, d30128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98221 q ha hb
  have h2 (q : Pattern) (ha : d39730 q = 1) (hb : d287734 q = 1) : d30129 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39730, d30129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39730, d30129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39731 q = 1) (hb : d287734 q = 1) : d30130 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39731, d30130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39731, d30130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39734 q = 1) (hb : d287734 q = 1) : d30141 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39734, d30141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98221 q ha hb
    | true =>
      simp only [d39734, d30141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98223 q ha hb
  have h5 (q : Pattern) (ha : d39735 q = 1) (hb : d287734 q = 1) : d30142 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39735, d30142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39735, d30142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39736 q = 1) (hb : d287734 q = 1) : d30143 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39736, d30143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39736, d30143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39737 q = 1) (hb : d287734 q = 1) : d30144 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39737, d30144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39737, d30144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39738 q = 1) (hb : d287734 q = 1) : d30145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39738, d30145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39738, d30145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39739 q = 1) (hb : d287734 q = 1) : d30146 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39739, d30146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39739, d30146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39740 q = 1) (hb : d287734 q = 1) : d30147 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39740, d30147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39740, d30147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro98225 (p : Pattern) (ha : d39744 p = 1) (hb : d287734 p = 1) : d30151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39734 q = 1) (hb : d287734 q = 1) : d30141 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39734, d30141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98221 q ha hb
    | true =>
      simp only [d39734, d30141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98223 q ha hb
  have h2 (q : Pattern) (ha : d39735 q = 1) (hb : d287734 q = 1) : d30142 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39735, d30142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39735, d30142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39736 q = 1) (hb : d287734 q = 1) : d30143 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39736, d30143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39736, d30143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39738 q = 1) (hb : d287734 q = 1) : d30145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39738, d30145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39738, d30145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39743 q = 1) (hb : d287734 q = 1) : d30150 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39743, d30150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39743, d30150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39744 q = 1) (hb : d287734 q = 1) : d30151 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39744, d30151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39744, d30151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98226 (p : Pattern) (ha : d39750 p = 1) (hb : d287734 p = 1) : d30157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d287734 q = 1) : d30148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d30148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98224 q ha hb
    | true =>
      simp only [d39741, d30148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d287734 q = 1) : d30149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d30149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d30149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d287734 q = 1) : d30152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98225 q ha hb
    | true =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d287734 q = 1) : d30153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d287734 q = 1) : d30154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d30154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d30154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39748 q = 1) (hb : d287734 q = 1) : d30155 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39748, d30155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39748, d30155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39749 q = 1) (hb : d287734 q = 1) : d30156 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39749, d30156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39749, d30156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39750 q = 1) (hb : d287734 q = 1) : d30157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39750, d30157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39750, d30157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98227 (p : Pattern) (ha : d39754 p = 1) (hb : d287734 p = 1) : d30161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d287734 q = 1) : d30152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98225 q ha hb
    | true =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d287734 q = 1) : d30153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d287734 q = 1) : d30158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d30158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d30158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39752 q = 1) (hb : d287734 q = 1) : d30159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39752, d30159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39752, d30159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39753 q = 1) (hb : d287734 q = 1) : d30160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39753, d30160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39753, d30160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39754 q = 1) (hb : d287734 q = 1) : d30161 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39754, d30161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39754, d30161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98228 (p : Pattern) (ha : d39760 p = 1) (hb : d287734 p = 1) : d30167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39755 q = 1) (hb : d287734 q = 1) : d30162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39755, d30162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98226 q ha hb
    | true =>
      simp only [d39755, d30162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98227 q ha hb
  have h2 (q : Pattern) (ha : d39756 q = 1) (hb : d287734 q = 1) : d30163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39756, d30163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39756, d30163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39757 q = 1) (hb : d287734 q = 1) : d30164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39757, d30164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39757, d30164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39758 q = 1) (hb : d287734 q = 1) : d30165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39758, d30165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39758, d30165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39759 q = 1) (hb : d287734 q = 1) : d30166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39759, d30166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39759, d30166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39760 q = 1) (hb : d287734 q = 1) : d30167 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39760, d30167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39760, d30167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98229 (p : Pattern) (ha : d39763 p = 1) (hb : d287734 p = 1) : d30170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d287734 q = 1) : d30148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d30148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98224 q ha hb
    | true =>
      simp only [d39741, d30148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d287734 q = 1) : d30149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d30149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d30149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d287734 q = 1) : d30152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98225 q ha hb
    | true =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d287734 q = 1) : d30153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d287734 q = 1) : d30154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d30154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d30154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39748 q = 1) (hb : d287734 q = 1) : d30155 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39748, d30155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39748, d30155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39749 q = 1) (hb : d287734 q = 1) : d30156 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39749, d30156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39749, d30156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39763 q = 1) (hb : d287734 q = 1) : d30170 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39763, d30170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39763, d30170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98230 (p : Pattern) (ha : d39764 p = 1) (hb : d287734 p = 1) : d30171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d287734 q = 1) : d30152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98225 q ha hb
    | true =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d287734 q = 1) : d30153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d287734 q = 1) : d30158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d30158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d30158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39752 q = 1) (hb : d287734 q = 1) : d30159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39752, d30159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39752, d30159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39753 q = 1) (hb : d287734 q = 1) : d30160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39753, d30160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39753, d30160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39764 q = 1) (hb : d287734 q = 1) : d30171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39764, d30171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39764, d30171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98231 (p : Pattern) (ha : d39770 p = 1) (hb : d287734 p = 1) : d30177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39755 q = 1) (hb : d287734 q = 1) : d30162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39755, d30162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98226 q ha hb
    | true =>
      simp only [d39755, d30162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98227 q ha hb
  have h2 (q : Pattern) (ha : d39756 q = 1) (hb : d287734 q = 1) : d30163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39756, d30163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39756, d30163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39757 q = 1) (hb : d287734 q = 1) : d30164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39757, d30164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39757, d30164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39758 q = 1) (hb : d287734 q = 1) : d30165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39758, d30165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39758, d30165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39759 q = 1) (hb : d287734 q = 1) : d30166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39759, d30166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39759, d30166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39765 q = 1) (hb : d287734 q = 1) : d30172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39765, d30172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98229 q ha hb
    | true =>
      simp only [d39765, d30172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98230 q ha hb
  have h7 (q : Pattern) (ha : d39766 q = 1) (hb : d287734 q = 1) : d30173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39766, d30173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39766, d30173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39767 q = 1) (hb : d287734 q = 1) : d30174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39767, d30174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39767, d30174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39768 q = 1) (hb : d287734 q = 1) : d30175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39768, d30175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39768, d30175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39769 q = 1) (hb : d287734 q = 1) : d30176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39769, d30176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39769, d30176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39770 q = 1) (hb : d287734 q = 1) : d30177 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39770, d30177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39770, d30177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98232 (p : Pattern) (ha : d39926 p = 1) (hb : d287734 p = 1) : d30378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39755 q = 1) (hb : d287734 q = 1) : d30162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39755, d30162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98226 q ha hb
    | true =>
      simp only [d39755, d30162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98227 q ha hb
  have h2 (q : Pattern) (ha : d39756 q = 1) (hb : d287734 q = 1) : d30163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39756, d30163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39756, d30163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39757 q = 1) (hb : d287734 q = 1) : d30164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39757, d30164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39757, d30164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39758 q = 1) (hb : d287734 q = 1) : d30165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39758, d30165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39758, d30165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39759 q = 1) (hb : d287734 q = 1) : d30166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39759, d30166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39759, d30166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39921 q = 1) (hb : d287734 q = 1) : d30373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39921, d30373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98227 q ha hb
    | true =>
      simp only [d39921, d30373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39922 q = 1) (hb : d287734 q = 1) : d30374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39922, d30374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39922, d30374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39923 q = 1) (hb : d287734 q = 1) : d30375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39923, d30375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39923, d30375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39924 q = 1) (hb : d287734 q = 1) : d30376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39924, d30376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39924, d30376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39925 q = 1) (hb : d287734 q = 1) : d30377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39925, d30377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39925, d30377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39926 q = 1) (hb : d287734 q = 1) : d30378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39926, d30378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39926, d30378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98233 (p : Pattern) (ha : d39932 p = 1) (hb : d287734 p = 1) : d30384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39921 q = 1) (hb : d287734 q = 1) : d30373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39921, d30373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98227 q ha hb
    | true =>
      simp only [d39921, d30373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39922 q = 1) (hb : d287734 q = 1) : d30374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39922, d30374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39922, d30374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39923 q = 1) (hb : d287734 q = 1) : d30375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39923, d30375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39923, d30375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39924 q = 1) (hb : d287734 q = 1) : d30376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39924, d30376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39924, d30376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39925 q = 1) (hb : d287734 q = 1) : d30377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39925, d30377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39925, d30377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39927 q = 1) (hb : d287734 q = 1) : d30379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39927, d30379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98230 q ha hb
    | true =>
      simp only [d39927, d30379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39928 q = 1) (hb : d287734 q = 1) : d30380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39928, d30380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39928, d30380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39929 q = 1) (hb : d287734 q = 1) : d30381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39929, d30381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39929, d30381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39930 q = 1) (hb : d287734 q = 1) : d30382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39930, d30382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39930, d30382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39931 q = 1) (hb : d287734 q = 1) : d30383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39931, d30383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39931, d30383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39932 q = 1) (hb : d287734 q = 1) : d30384 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39932, d30384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39932, d30384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98234 (p : Pattern) (ha : d39941 p = 1) (hb : d287734 p = 1) : d30393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39927 q = 1) (hb : d287734 q = 1) : d30379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39927, d30379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98230 q ha hb
    | true =>
      simp only [d39927, d30379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39928 q = 1) (hb : d287734 q = 1) : d30380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39928, d30380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39928, d30380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39929 q = 1) (hb : d287734 q = 1) : d30381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39929, d30381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39929, d30381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39930 q = 1) (hb : d287734 q = 1) : d30382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39930, d30382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39930, d30382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39931 q = 1) (hb : d287734 q = 1) : d30383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39931, d30383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39931, d30383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39941 q = 1) (hb : d287734 q = 1) : d30393 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39941, d30393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39941, d30393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98235 (p : Pattern) (ha : d39971 p = 1) (hb : d287734 p = 1) : d30438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39962 q = 1) (hb : d287734 q = 1) : d30429 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39962, d30429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39962, d30429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98219 q ha hb
  have h2 (q : Pattern) (ha : d39717 q = 1) (hb : d287734 q = 1) : d30116 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39717, d30116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98219 q ha hb
    | true =>
      simp only [d39717, d30116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39963 q = 1) (hb : d287734 q = 1) : d30430 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39963, d30430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39963, d30430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39718 q = 1) (hb : d287734 q = 1) : d30117 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39718, d30117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39718, d30117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39964 q = 1) (hb : d287734 q = 1) : d30431 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39964, d30431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39964, d30431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39965 q = 1) (hb : d287734 q = 1) : d30432 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39965, d30432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39965, d30432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39966 q = 1) (hb : d287734 q = 1) : d30433 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39966, d30433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39966, d30433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98220 q ha hb
  have h8 (q : Pattern) (ha : d39722 q = 1) (hb : d287734 q = 1) : d30121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d30121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98220 q ha hb
    | true =>
      simp only [d39722, d30121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39967 q = 1) (hb : d287734 q = 1) : d30434 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39967, d30434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39967, d30434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39723 q = 1) (hb : d287734 q = 1) : d30122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d30122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39723, d30122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39968 q = 1) (hb : d287734 q = 1) : d30435 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39968, d30435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39968, d30435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d39969 q = 1) (hb : d287734 q = 1) : d30436 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39969, d30436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d39969, d30436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d39970 q = 1) (hb : d287734 q = 1) : d30437 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39970, d30437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39970, d30437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39947 q = 1) (hb : d287734 q = 1) : d30414 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39947, d30414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39947, d30414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98217 q ha hb
  have h15 (q : Pattern) (ha : d39705 q = 1) (hb : d287734 q = 1) : d30107 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d30107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98217 q ha hb
    | true =>
      simp only [d39705, d30107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d39948 q = 1) (hb : d287734 q = 1) : d30415 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39948, d30415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d39948, d30415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d39706 q = 1) (hb : d287734 q = 1) : d30108 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d30108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d39706, d30108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d39949 q = 1) (hb : d287734 q = 1) : d30416 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39949, d30416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d39949, d30416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d39950 q = 1) (hb : d287734 q = 1) : d30417 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39950, d30417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d39950, d30417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d39956 q = 1) (hb : d287734 q = 1) : d30423 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39956, d30423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d39956, d30423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d39971 q = 1) (hb : d287734 q = 1) : d30438 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39971, d30438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39971, d30438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro98236 (p : Pattern) (ha : d39976 p = 1) (hb : d287734 p = 1) : d30448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39966 q = 1) (hb : d287734 q = 1) : d30433 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39966, d30433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39966, d30433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98220 q ha hb
  have h2 (q : Pattern) (ha : d39722 q = 1) (hb : d287734 q = 1) : d30121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d30121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98220 q ha hb
    | true =>
      simp only [d39722, d30121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39967 q = 1) (hb : d287734 q = 1) : d30434 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39967, d30434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39967, d30434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39723 q = 1) (hb : d287734 q = 1) : d30122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d30122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39723, d30122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39968 q = 1) (hb : d287734 q = 1) : d30435 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39968, d30435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39968, d30435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39969 q = 1) (hb : d287734 q = 1) : d30436 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39969, d30436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39969, d30436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39975 q = 1) (hb : d287734 q = 1) : d30442 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39975, d30442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39975, d30442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d287734 q = 1) : d30443 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d30443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d30443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98222 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d287734 q = 1) : d30135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d30135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98222 q ha hb
    | true =>
      simp only [d10412, d30135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d287734 q = 1) : d30444 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d30444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d30444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d287734 q = 1) : d30136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d30136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d30136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d287734 q = 1) : d30445 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d30445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d30445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d287734 q = 1) : d30446 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d30446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d30446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d287734 q = 1) : d30447 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d30447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d30447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39976 q = 1) (hb : d287734 q = 1) : d30448 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39976, d30448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39976, d30448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98237 (p : Pattern) (ha : d39995 p = 1) (hb : d287734 p = 1) : d30467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39977 q = 1) (hb : d287734 q = 1) : d30449 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39977, d30449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98235 q ha hb
    | true =>
      simp only [d39977, d30449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98236 q ha hb
  have h2 (q : Pattern) (ha : d39978 q = 1) (hb : d287734 q = 1) : d30450 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39978, d30450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39978, d30450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39979 q = 1) (hb : d287734 q = 1) : d30451 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39979, d30451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39979, d30451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39985 q = 1) (hb : d287734 q = 1) : d30457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39985, d30457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39985, d30457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39994 q = 1) (hb : d287734 q = 1) : d30466 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39994, d30466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39994, d30466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39995 q = 1) (hb : d287734 q = 1) : d30467 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39995, d30467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39995, d30467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98238 (p : Pattern) (ha : d40082 p = 1) (hb : d287734 p = 1) : d30568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39996 q = 1) (hb : d287734 q = 1) : d30468 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39996, d30468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98237 q ha hb
    | true =>
      simp only [d39996, d30468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39997 q = 1) (hb : d287734 q = 1) : d30469 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39997, d30469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39997, d30469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40079 q = 1) (hb : d287734 q = 1) : d30565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d40079, d30565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40079, d30565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40080 q = 1) (hb : d287734 q = 1) : d30566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40080, d30566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40080, d30566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d40081 q = 1) (hb : d287734 q = 1) : d30567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d40081, d30567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40081, d30567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d40082 q = 1) (hb : d287734 q = 1) : d30568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d40082, d30568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40082, d30568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98239 (p : Pattern) (ha : d40088 p = 1) (hb : d287734 p = 1) : d30574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40083 q = 1) (hb : d287734 q = 1) : d30569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40083, d30569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98238 q ha hb
    | true =>
      simp only [d40083, d30569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d40084 q = 1) (hb : d287734 q = 1) : d30570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40084, d30570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40084, d30570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40085 q = 1) (hb : d287734 q = 1) : d30571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40085, d30571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40085, d30571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40086 q = 1) (hb : d287734 q = 1) : d30572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40086, d30572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40086, d30572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40087 q = 1) (hb : d287734 q = 1) : d30573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40087, d30573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40087, d30573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40088 q = 1) (hb : d287734 q = 1) : d30574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d40088, d30574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40088, d30574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98240 (p : Pattern) (ha : d39775 p = 1) (hb : d287734 p = 1) : d30182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d287734 q = 1) : d30148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d30148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98224 q ha hb
    | true =>
      simp only [d39741, d30148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d287734 q = 1) : d30149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d30149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d30149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d287734 q = 1) : d30152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98225 q ha hb
    | true =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d287734 q = 1) : d30153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d287734 q = 1) : d30154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d30154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d30154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39748 q = 1) (hb : d287734 q = 1) : d30155 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39748, d30155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39748, d30155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39774 q = 1) (hb : d287734 q = 1) : d30181 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39774, d30181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39774, d30181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39775 q = 1) (hb : d287734 q = 1) : d30182 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39775, d30182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39775, d30182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98241 (p : Pattern) (ha : d39777 p = 1) (hb : d287734 p = 1) : d30184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d287734 q = 1) : d30152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98225 q ha hb
    | true =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d287734 q = 1) : d30153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d287734 q = 1) : d30158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d30158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d30158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39752 q = 1) (hb : d287734 q = 1) : d30159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39752, d30159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39752, d30159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39776 q = 1) (hb : d287734 q = 1) : d30183 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39776, d30183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39776, d30183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39777 q = 1) (hb : d287734 q = 1) : d30184 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39777, d30184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39777, d30184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98242 (p : Pattern) (ha : d39784 p = 1) (hb : d287734 p = 1) : d30191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39741 q = 1) (hb : d287734 q = 1) : d30148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d30148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98224 q ha hb
    | true =>
      simp only [d39741, d30148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39742 q = 1) (hb : d287734 q = 1) : d30149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d30149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d30149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39745 q = 1) (hb : d287734 q = 1) : d30152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98225 q ha hb
    | true =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39746 q = 1) (hb : d287734 q = 1) : d30153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39747 q = 1) (hb : d287734 q = 1) : d30154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39747, d30154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39747, d30154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39782 q = 1) (hb : d287734 q = 1) : d30189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39782, d30189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39782, d30189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39783 q = 1) (hb : d287734 q = 1) : d30190 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39783, d30190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39783, d30190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39784 q = 1) (hb : d287734 q = 1) : d30191 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39784, d30191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39784, d30191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98243 (p : Pattern) (ha : d39787 p = 1) (hb : d287734 p = 1) : d30194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39745 q = 1) (hb : d287734 q = 1) : d30152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98225 q ha hb
    | true =>
      simp only [d39745, d30152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39746 q = 1) (hb : d287734 q = 1) : d30153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39746, d30153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39751 q = 1) (hb : d287734 q = 1) : d30158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39751, d30158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39751, d30158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39785 q = 1) (hb : d287734 q = 1) : d30192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39785, d30192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39785, d30192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39786 q = 1) (hb : d287734 q = 1) : d30193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39786, d30193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39786, d30193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39787 q = 1) (hb : d287734 q = 1) : d30194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39787, d30194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39787, d30194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98244 (p : Pattern) (ha : d39794 p = 1) (hb : d287734 p = 1) : d30208 p = 1 := by
  have h0 (q : Pattern) (ha : d30101 q = 1) (hb : d287734 q = 1) : d30101 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d39705 q = 1) (hb : d287734 q = 1) : d30107 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39705, d30107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98217 q ha hb
    | true =>
      simp only [d39705, d30107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39706 q = 1) (hb : d287734 q = 1) : d30108 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39706, d30108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39706, d30108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d39707 q = 1) (hb : d287734 q = 1) : d30109 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39707, d30109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39707, d30109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39708 q = 1) (hb : d287734 q = 1) : d30110 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39708, d30110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39708, d30110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d39709 q = 1) (hb : d287734 q = 1) : d30111 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39709, d30111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39709, d30111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39727 q = 1) (hb : d287734 q = 1) : d30126 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39727, d30126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39727, d30126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d39794 q = 1) (hb : d287734 q = 1) : d30208 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39794, d30208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39794, d30208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98245 (p : Pattern) (ha : d39800 p = 1) (hb : d287734 p = 1) : d30214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30204 q = 1) (hb : d287734 q = 1) : d30204 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d39791 q = 1) (hb : d287734 q = 1) : d30205 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39791, d30205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39791, d30205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98218 q ha hb
  have h3 (q : Pattern) (ha : d39792 q = 1) (hb : d287734 q = 1) : d30206 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39792, d30206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39792, d30206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39793 q = 1) (hb : d287734 q = 1) : d30207 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39793, d30207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39793, d30207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39795 q = 1) (hb : d287734 q = 1) : d30209 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39795, d30209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98218 q ha hb
    | true =>
      simp only [d39795, d30209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98244 q ha hb
  have h6 (q : Pattern) (ha : d39796 q = 1) (hb : d287734 q = 1) : d30210 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39796, d30210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39796, d30210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d39797 q = 1) (hb : d287734 q = 1) : d30211 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39797, d30211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39797, d30211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39798 q = 1) (hb : d287734 q = 1) : d30212 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39798, d30212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39798, d30212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d39729 q = 1) (hb : d287734 q = 1) : d30128 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39729, d30128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98218 q ha hb
    | true =>
      simp only [d39729, d30128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98221 q ha hb
  have h10 (q : Pattern) (ha : d39730 q = 1) (hb : d287734 q = 1) : d30129 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39730, d30129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39730, d30129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39731 q = 1) (hb : d287734 q = 1) : d30130 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39731, d30130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39731, d30130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d39734 q = 1) (hb : d287734 q = 1) : d30141 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39734, d30141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98221 q ha hb
    | true =>
      simp only [d39734, d30141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98223 q ha hb
  have h13 (q : Pattern) (ha : d39735 q = 1) (hb : d287734 q = 1) : d30142 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39735, d30142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39735, d30142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39736 q = 1) (hb : d287734 q = 1) : d30143 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39736, d30143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39736, d30143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d39737 q = 1) (hb : d287734 q = 1) : d30144 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39737, d30144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d39737, d30144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d39799 q = 1) (hb : d287734 q = 1) : d30213 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39799, d30213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39799, d30213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d39800 q = 1) (hb : d287734 q = 1) : d30214 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39800, d30214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d39800, d30214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro98246 (p : Pattern) (ha : d39806 p = 1) (hb : d287734 p = 1) : d30220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39801 q = 1) (hb : d287734 q = 1) : d30215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39801, d30215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98245 q ha hb
    | true =>
      simp only [d39801, d30215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39802 q = 1) (hb : d287734 q = 1) : d30216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39802, d30216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39802, d30216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39741 q = 1) (hb : d287734 q = 1) : d30148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39741, d30148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98224 q ha hb
    | true =>
      simp only [d39741, d30148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39742 q = 1) (hb : d287734 q = 1) : d30149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39742, d30149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39742, d30149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39803 q = 1) (hb : d287734 q = 1) : d30217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39803, d30217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39803, d30217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39804 q = 1) (hb : d287734 q = 1) : d30218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39804, d30218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39804, d30218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39805 q = 1) (hb : d287734 q = 1) : d30219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39805, d30219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39805, d30219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39806 q = 1) (hb : d287734 q = 1) : d30220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39806, d30220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39806, d30220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98247 (p : Pattern) (ha : d39861 p = 1) (hb : d287734 p = 1) : d30314 p = 1 := by
  have h0 (q : Pattern) (ha : d30311 q = 1) (hb : d287734 q = 1) : d30311 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2046 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5238 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5239 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2048 q = 1) (hb : d287734 q = 1) : d2048 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5243 q = 1) (hb : d287734 q = 1) : d30103 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5243, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2061 q = 1) (hb : d287734 q = 1) : d2061 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5244 q = 1) (hb : d287734 q = 1) : d30312 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d30312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5244, d30312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5245 q = 1) (hb : d287734 q = 1) : d30313 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d30313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5245, d30313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d39861 q = 1) (hb : d287734 q = 1) : d30314 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39861, d30314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39861, d30314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98248 (p : Pattern) (ha : d39867 p = 1) (hb : d287734 p = 1) : d30320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39717 q = 1) (hb : d287734 q = 1) : d30116 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39717, d30116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98219 q ha hb
    | true =>
      simp only [d39717, d30116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39718 q = 1) (hb : d287734 q = 1) : d30117 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39718, d30117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39718, d30117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39719 q = 1) (hb : d287734 q = 1) : d30118 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39719, d30118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39719, d30118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39720 q = 1) (hb : d287734 q = 1) : d30119 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39720, d30119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39720, d30119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39722 q = 1) (hb : d287734 q = 1) : d30121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39722, d30121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98220 q ha hb
    | true =>
      simp only [d39722, d30121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39723 q = 1) (hb : d287734 q = 1) : d30122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39723, d30122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39723, d30122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39724 q = 1) (hb : d287734 q = 1) : d30123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39724, d30123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39724, d30123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39725 q = 1) (hb : d287734 q = 1) : d30124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39725, d30124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39725, d30124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39726 q = 1) (hb : d287734 q = 1) : d30125 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39726, d30125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39726, d30125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39862 q = 1) (hb : d287734 q = 1) : d30315 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39862, d30315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98247 q ha hb
    | true =>
      simp only [d39862, d30315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39863 q = 1) (hb : d287734 q = 1) : d30316 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39863, d30316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39863, d30316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d39864 q = 1) (hb : d287734 q = 1) : d30317 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39864, d30317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39864, d30317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39865 q = 1) (hb : d287734 q = 1) : d30318 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39865, d30318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39865, d30318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d39866 q = 1) (hb : d287734 q = 1) : d30319 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39866, d30319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39866, d30319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39867 q = 1) (hb : d287734 q = 1) : d30320 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39867, d30320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39867, d30320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98249 (p : Pattern) (ha : d39871 p = 1) (hb : d287734 p = 1) : d30323 p = 1 := by
  have h0 (q : Pattern) (ha : d30083 q = 1) (hb : d287734 q = 1) : d30083 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2046 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5238 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d287734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5239 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39868 q = 1) (hb : d287734 q = 1) : d30309 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d39868, d30309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39868, d30309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30103 q = 1) (hb : d287734 q = 1) : d30103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d39869 q = 1) (hb : d287734 q = 1) : d30321 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d39869, d30321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39869, d30321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d39870 q = 1) (hb : d287734 q = 1) : d30322 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d39870, d30322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d39870, d30322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d287734 q = 1) : d2048 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5243 q = 1) (hb : d287734 q = 1) : d30103 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5243, d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2061 q = 1) (hb : d287734 q = 1) : d2061 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5244 q = 1) (hb : d287734 q = 1) : d30312 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d30312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5244, d30312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5245 q = 1) (hb : d287734 q = 1) : d30313 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d30313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5245, d30313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d39871 q = 1) (hb : d287734 q = 1) : d30323 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d39871, d30323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39871, d30323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
